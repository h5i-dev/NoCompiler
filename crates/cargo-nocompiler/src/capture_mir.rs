use crate::contract_ir::{Access, Expr, Input, Pointer, Summary, ViewEnd};
use rustc_ast::InlineAsmOptions;
use rustc_middle::{
    mir::{
        self, AggregateKind, BinOp, Body, CastKind, Local, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind, UnOp, visit::Visitor,
    },
    ty::{self, Instance, Ty, TyCtxt, TypingEnv},
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Scalar(Expr),
    Address(Pointer),
    End(ViewEnd),
    Functions(BTreeSet<String>),
}
#[derive(Clone, Default, PartialEq, Eq)]
struct State {
    locals: BTreeMap<Local, Value>,
    fields: BTreeMap<(usize, u64), Expr>,
    initialized: BTreeSet<(usize, u64)>,
}
#[derive(Default)]
struct Moves<'tcx>(Vec<Place<'tcx>>);

impl<'tcx> Visitor<'tcx> for Moves<'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, _location: mir::Location) {
        if let Operand::Move(place) = operand {
            self.0.push(*place);
        }
    }
}

impl Value {
    fn view_end(&self, stride: u64) -> Option<ViewEnd> {
        match self {
            Self::Address(view) => Some(ViewEnd {
                argument: view.argument,
                stride,
                end: view.offset.add(view.length.as_ref()?, stride.into())?,
            }),
            Self::End(view) if view.stride == stride => Some(view.clone()),
            _ => None,
        }
    }
}

impl State {
    fn forget_fields(&mut self) {
        self.fields.clear();
        self.initialized.clear();
    }
}

impl State {
    fn meet(&mut self, other: &Self, stride: impl Fn(Local) -> Option<u64>) -> bool {
        let mut changed = false;
        self.locals.retain(|local, value| {
            if other.locals.get(local) == Some(value) {
                return true;
            }
            if let (Value::Functions(targets), Some(Value::Functions(other))) =
                (&mut *value, other.locals.get(local))
            {
                let before = targets.len();
                targets.extend(other.iter().cloned());
                changed |= targets.len() != before;
                return targets.len() <= 8;
            }
            let shared = stride(*local).and_then(|stride| {
                let end = value.view_end(stride)?;
                (other.locals.get(local)?.view_end(stride)? == end).then_some(end)
            });
            if let Some(end) = shared {
                changed |= *value != Value::End(end.clone());
                *value = Value::End(end);
                true
            } else {
                changed = true;
                false
            }
        });
        let before = self.fields.len();
        self.fields
            .retain(|key, value| other.fields.get(key) == Some(value));
        let initialized = self.initialized.len();
        self.initialized.retain(|key| other.initialized.contains(key));
        changed || before != self.fields.len() || initialized != self.initialized.len()
    }
}
// Preserve a small number of correlated paths. Widen once at a busy merge
// or a loop, keeping common relations in the widened state.
enum Paths {
    Distinct(Vec<State>),
    Widened(State),
}

impl Paths {
    fn states(&self) -> &[State] {
        match self {
            Self::Distinct(paths) => paths,
            Self::Widened(state) => std::slice::from_ref(state),
        }
    }

    fn insert(&mut self, state: State, stride: impl Fn(Local) -> Option<u64>) -> bool {
        const MAX_PATHS: usize = 4;
        match self {
            Self::Widened(merged) => merged.meet(&state, stride),
            Self::Distinct(paths) if paths.contains(&state) => false,
            Self::Distinct(paths) if paths.len() < MAX_PATHS => {
                paths.push(state);
                true
            }
            Self::Distinct(paths) => {
                let mut merged = state;
                for path in paths {
                    merged.meet(path, &stride);
                }
                *self = Self::Widened(merged);
                true
            }
        }
    }
}

struct Analyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &'a Body<'tcx>,
    env: TypingEnv<'tcx>,
    summaries: &'a BTreeMap<String, Summary>,
}

impl<'tcx> Analyzer<'_, 'tcx> {
    fn ty(&self, ty: Ty<'tcx>) -> Ty<'tcx> {
        self.instance.instantiate_mir_and_normalize_erasing_regions(
            self.tcx,
            self.env,
            ty::EarlyBinder::bind(self.tcx, ty),
        )
    }
    fn layout(&self, ty: Ty<'tcx>) -> Option<rustc_middle::ty::layout::TyAndLayout<'tcx>> {
        self.tcx.layout_of(self.env.as_query_input(ty)).ok()
    }
    fn referent(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _) => Some(*pointee),
            ty::Adt(_, args) if ty.is_box() => Some(args.type_at(0)),
            _ => None,
        }
    }
    fn view_stride(&self, ty: Ty<'tcx>) -> Option<u64> {
        let pointee = self.referent(ty)?;
        let ty::Slice(element) = pointee.kind() else {
            return None;
        };
        let size = self.layout(*element)?.size.bytes();
        (size != 0).then_some(size)
    }
    fn place_ty(&self, place: Place<'tcx>) -> Ty<'tcx> {
        self.ty(place.ty(&self.body.local_decls, self.tcx).ty)
    }
    fn operand_ty(&self, operand: &Operand<'tcx>) -> Ty<'tcx> {
        self.ty(operand.ty(&self.body.local_decls, self.tcx))
    }
    fn element(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        match ty.kind() {
            ty::Array(t, _) | ty::Slice(t) => Some(*t),
            _ => None,
        }
    }
    fn address(&self, place: Place<'tcx>, state: &State) -> Option<Pointer> {
        let (first, projections) = place.projection.split_first()?;
        let ProjectionElem::Deref = first else {
            return None;
        };
        let Value::Address(mut pointer) = state.locals.get(&place.local)?.clone() else {
            return None;
        };
        let mut ty = self.referent(self.ty(self.body.local_decls[place.local].ty))?;
        for projection in projections {
            match *projection {
                ProjectionElem::Field(field, field_ty) => {
                    let layout = self.layout(ty)?;
                    let offset = layout.fields.offset(field.as_usize()).bytes();
                    pointer.offset = pointer.offset.add(&Expr::constant(offset.into()), 1)?;
                    ty = self.ty(field_ty);
                    pointer.length = self.array_length(ty);
                }
                ProjectionElem::Index(local) => {
                    let Value::Scalar(index) = state.locals.get(&local)? else {
                        return None;
                    };
                    ty = self.element(ty)?;
                    pointer.offset = pointer
                        .offset
                        .add(index, i128::from(self.layout(ty)?.size.bytes()))?;
                    pointer.length = None;
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let mut index = Expr::constant(offset.into());
                    if from_end {
                        index = pointer.length.as_ref()?.add(&index, -1)?;
                    }
                    ty = self.element(ty)?;
                    pointer.offset = pointer
                        .offset
                        .add(&index, i128::from(self.layout(ty)?.size.bytes()))?;
                    pointer.length = None;
                }
                ProjectionElem::Subslice { from, to, from_end } => {
                    let width = i128::from(self.layout(self.element(ty)?)?.size.bytes());
                    pointer.offset = pointer
                        .offset
                        .add(&Expr::constant(i128::from(from).checked_mul(width)?), 1)?;
                    pointer.length = if from_end {
                        Some(
                            pointer
                                .length
                                .as_ref()?
                                .add(&Expr::constant(i128::from(from) + i128::from(to)), -1)?,
                        )
                    } else {
                        Some(Expr::constant(i128::from(to) - i128::from(from)))
                    };
                }
                _ => return None,
            }
        }
        Some(pointer)
    }
    fn array_length(&self, ty: Ty<'tcx>) -> Option<Expr> {
        match ty.kind() {
            ty::Array(_, len) => Some(Expr::constant(len.try_to_target_usize(self.tcx)?.into())),
            _ => None,
        }
    }
    fn memory(&self, place: Place<'tcx>, state: &State, write: bool, out: &mut Summary) {
        if !place
            .projection
            .iter()
            .any(|p| matches!(p, ProjectionElem::Deref))
        {
            return;
        }
        if let Some(pointer) = self.address(place, state)
            && let Some(layout) = self.layout(self.place_ty(place))
            && layout.is_sized()
        {
            out.accesses.insert(Access {
                argument: pointer.argument,
                offset: pointer.offset,
                bytes: Expr::constant(layout.size.bytes().into()),
                alignment: layout.align.abi.bytes(),
                write,
            });
        } else {
            out.unresolved_access = true;
        }
    }
    fn operand(&self, operand: &Operand<'tcx>, state: &State, out: &mut Summary) -> Option<Value> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.memory(*place, state, false, out);
                if place.projection.is_empty() {
                    state.locals.get(&place.local).cloned()
                } else {
                    let address = self.address(*place, state)?;
                    let offset = u64::try_from(address.offset.constant).ok()?;
                    address.offset.terms.is_empty().then_some(())?;
                    state
                        .fields
                        .get(&(address.argument, offset))
                        .cloned()
                        .map(Value::Scalar)
                }
            }
            Operand::Constant(c) => {
                let constant = self.instance.instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    self.env,
                    ty::EarlyBinder::bind(self.tcx, c.const_),
                );
                if let Some(instance) = self.direct_callee(operand) {
                    return Some(Value::Functions(BTreeSet::from([
                        self.tcx.symbol_name(instance).name.to_owned()
                    ])));
                }
                if !matches!(constant.ty().kind(), ty::Int(_) | ty::Uint(_) | ty::Bool) {
                    return None;
                }
                let bits = constant.try_eval_bits(self.tcx, self.env)?;
                let value = if matches!(constant.ty().kind(), ty::Int(_)) {
                    let width = self.layout(self.ty(constant.ty()))?.size.bits();
                    ((bits << (128 - width)) as i128) >> (128 - width)
                } else {
                    i128::try_from(bits).ok()?
                };
                Some(Value::Scalar(Expr::constant(value)))
            }
            _ => None,
        }
    }
    fn value(&self, rvalue: &Rvalue<'tcx>, state: &State, out: &mut Summary) -> Option<Value> {
        match rvalue {
            Rvalue::Use(operand, _) => self.operand(operand, state, out),
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                if let Some(Value::End(end)) = state.locals.get(&place.local) {
                    match &place.projection[..] {
                        [ProjectionElem::Deref] => return Some(Value::End(end.clone())),
                        [
                            ProjectionElem::Deref,
                            ProjectionElem::Subslice {
                                to, from_end: true, ..
                            },
                        ] => {
                            let mut result = end.clone();
                            let removed = i128::from(*to).checked_mul(i128::from(end.stride))?;
                            result.end = end.end.add(&Expr::constant(removed), -1)?;
                            return Some(Value::End(result));
                        }
                        _ => {}
                    }
                }
                self.address(*place, state).map(Value::Address)
            }
            Rvalue::CopyForDeref(place) => self.operand(&Operand::Copy(*place), state, out),
            Rvalue::Cast(CastKind::PtrToPtr | CastKind::PointerCoercion(..), operand, _) => {
                match self.operand(operand, state, out)? {
                    value @ (Value::Address(_) | Value::Functions(_)) => Some(value),
                    _ => None,
                }
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                let Value::Address(pointer) = self.operand(operand, state, out)? else {
                    return None;
                };
                pointer.length.map(Value::Scalar)
            }
            Rvalue::BinaryOp(op, box_operands) => {
                let (left, right) = &**box_operands;
                let a = self.operand(left, state, out);
                let b = self.operand(right, state, out);
                match (op, a?, b?) {
                    (BinOp::Add | BinOp::AddUnchecked, Value::Scalar(a), Value::Scalar(b)) => {
                        a.add(&b, 1).map(Value::Scalar)
                    }
                    (BinOp::Sub | BinOp::SubUnchecked, Value::Scalar(a), Value::Scalar(b)) => {
                        a.add(&b, -1).map(Value::Scalar)
                    }
                    (BinOp::Mul | BinOp::MulUnchecked, Value::Scalar(a), Value::Scalar(b))
                        if b.terms.is_empty() =>
                    {
                        a.scale(b.constant).map(Value::Scalar)
                    }
                    (BinOp::Offset, Value::Address(mut ptr), Value::Scalar(index)) => {
                        let element = self.referent(self.operand_ty(left))?;
                        ptr.offset = ptr
                            .offset
                            .add(&index, self.layout(element)?.size.bytes().into())?;
                        ptr.length = None;
                        Some(Value::Address(ptr))
                    }
                    _ => None,
                }
            }
            Rvalue::Aggregate(kind, operands) if matches!(**kind, AggregateKind::RawPtr(..)) => {
                let values: Vec<_> = operands
                    .iter()
                    .map(|o| self.operand(o, state, out))
                    .collect();
                let [Some(Value::Address(pointer)), Some(Value::Scalar(len))] = values.as_slice()
                else {
                    return None;
                };
                let mut pointer = pointer.clone();
                pointer.length = Some(len.clone());
                Some(Value::Address(pointer))
            }
            // Inspect loads embedded in computations whose values are not modelled.
            Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Repeat(operand, _) => {
                self.operand(operand, state, out);
                None
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    self.operand(operand, state, out);
                }
                None
            }
            _ => None,
        }
    }
    fn direct_callee(&self, operand: &Operand<'tcx>) -> Option<Instance<'tcx>> {
        let ty::FnDef(def, args) = self.operand_ty(operand).kind() else {
            return None;
        };
        if !matches!(
            self.tcx.def_kind(*def),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            return None;
        }
        Instance::try_resolve(self.tcx, self.env, *def, args.skip_binder())
            .ok()
            .flatten()
            .filter(|instance| matches!(instance.def, ty::InstanceKind::Item(_)))
    }

    fn forget_root(state: &mut State, out: &mut Summary, argument: usize) {
        out.drops.insert(argument);
        state.locals.retain(|_, value| match value {
            Value::Address(pointer) => pointer.argument != argument,
            Value::End(view) => view.argument != argument,
            Value::Scalar(_) | Value::Functions(_) => true,
        });
    }

    fn invalidate_place(&self, state: &mut State, place: Place<'tcx>) {
        if place.projection.is_empty() {
            state.locals.remove(&place.local);
        } else if place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref)) {
            if let Some(address) = self.address(place, state)
                && let Some(layout) = self.layout(self.place_ty(place)).filter(|layout| layout.is_sized())
            {
                Self::kill_write(state, address.argument, &address.offset,
                    &Expr::constant(layout.size.bytes().into()));
            } else {
                state.forget_fields();
            }
        }
    }

    fn kill_write(state: &mut State, argument: usize, offset: &Expr, size: &Expr) {
        let span = || {
            if !offset.terms.is_empty() || !size.terms.is_empty() {
                return None;
            }
            let start = u64::try_from(offset.constant).ok()?;
            let bytes = u64::try_from(size.constant).ok()?;
            Some((start, start.checked_add(bytes)?))
        };
        if let Some((start, end)) = span() {
            let separate = |base, word: u64| {
                start == end || (base == argument
                    && (word >= end || word.checked_add(8).is_some_and(|limit| limit <= start)))
            };
            state.fields.retain(|&(base, word), _| separate(base, word));
            state.initialized.retain(|&(base, word)| separate(base, word));
        } else {
            state.forget_fields();
        }
    }

    fn apply_summary(
        &self,
        summary: &Summary,
        args: &[Option<Value>],
        state: &mut State,
        out: &mut Summary,
    ) -> Option<Value> {
        let eval = |expr: &Expr| {
            let mut result = Expr::constant(expr.constant);
            for (&input, &scale) in &expr.terms {
                let value = match input {
                    Input::Value(index) => match args.get(index)?.as_ref()? {
                        Value::Scalar(value) => value,
                        _ => return None,
                    },
                    Input::Length(index) => match args.get(index)?.as_ref()? {
                        Value::Address(pointer) => pointer.length.as_ref()?,
                        _ => return None,
                    },
                };
                result = result.add(value, scale)?;
            }
            Some(result)
        };
        let resolve = |index: usize, relative: &Expr| {
            let Value::Address(root) = args.get(index)?.as_ref()? else {
                return None;
            };
            Some((root.argument, root.offset.add(&eval(relative)?, 1)?))
        };
        for access in &summary.accesses {
            if let Some((argument, offset)) = resolve(access.argument, &access.offset)
                && let Some(bytes) = eval(&access.bytes)
            {
                if access.write {
                    Self::kill_write(state, argument, &offset, &bytes);
                }
                out.accesses.insert(Access {
                    argument,
                    offset,
                    bytes,
                    ..access.clone()
                });
            } else {
                if access.write {
                    state.forget_fields();
                }
                out.unresolved_access = true;
            }
        }
        for &parameter in &summary.drops {
            if let Some((argument, _)) = resolve(parameter, &Expr::default()) {
                Self::forget_root(state, out, argument);
            }
        }
        if summary.unresolved_access || !summary.drops.is_empty() {
            state.forget_fields();
            out.unresolved_access = true;
            return None;
        }
        for &(parameter, offset) in &summary.initialized_words {
            if let Some((root, offset)) = resolve(parameter, &Expr::constant(offset.into()))
                && offset.terms.is_empty()
                && let Ok(offset) = offset.constant.try_into()
            {
                state.initialized.insert((root, offset));
            }
        }
        for (&(parameter, offset), value) in &summary.field_writes {
            if let Some((root, offset)) = resolve(parameter, &Expr::constant(offset.into()))
                && offset.terms.is_empty()
                && let Ok(offset) = offset.constant.try_into()
                && let Some(value) = eval(value)
            {
                state.fields.insert((root, offset), value);
            }
        }
        if let Some(value) = &summary.returned_scalar {
            return eval(value).map(Value::Scalar);
        }
        let view = summary.returned_view.as_ref()?;
        let (argument, offset) = resolve(view.argument, &view.offset)?;
        Some(Value::Address(Pointer {
            argument,
            offset,
            length: match &view.length {
                Some(length) => Some(eval(length)?),
                None => None,
            },
        }))
    }

    fn transfer(&self, index: mir::BasicBlock, mut state: State, out: &mut Summary) -> State {
        let block = &self.body.basic_blocks[index];
        for (statement_index, statement) in block.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    let value = self.value(rvalue, &state, out);
                    let mut moves = Moves::default();
                    moves.visit_rvalue(rvalue, mir::Location { block: index, statement_index });
                    for source in moves.0 {
                        self.invalidate_place(&mut state, source);
                    }
                    if place.projection.is_empty() {
                        state.locals.remove(&place.local);
                        if let Some(value) = value {
                            state.locals.insert(place.local, value);
                        }
                    } else if place
                        .projection
                        .iter()
                        .any(|p| matches!(p, ProjectionElem::Deref))
                    {
                        self.memory(*place, &state, true, out);
                        let location = self.address(*place, &state).and_then(|addr| {
                            let offset = u64::try_from(addr.offset.constant).ok()?;
                            addr.offset
                                .terms
                                .is_empty()
                                .then_some((addr.argument, offset))
                        });
                        let size = self
                            .layout(self.place_ty(*place))
                            .filter(|layout| layout.is_sized())
                            .map(|layout| layout.size.bytes());
                        if let (Some((argument, offset)), Some(size)) = (location, size) {
                            Self::kill_write(
                                &mut state,
                                argument,
                                &Expr::constant(offset.into()),
                                &Expr::constant(size.into()),
                            );
                            if size == 8 && crate::word_integer(self.place_ty(*place)) {
                                state.initialized.insert((argument, offset));
                                if let Some(Value::Scalar(expr)) = value {
                                    state.fields.insert((argument, offset), expr);
                                }
                            }
                        } else {
                            state.forget_fields();
                        }
                    }
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    state.locals.remove(local);
                }
                StatementKind::Intrinsic(intrinsic)
                    if let mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic =>
                {
                    let count = self.operand(&copy.count, &state, out);
                    for (operand, write) in [(&copy.src, false), (&copy.dst, true)] {
                        if let (Some(Value::Address(p)), Some(Value::Scalar(n))) =
                            (self.operand(operand, &state, out), count.as_ref())
                            && let Some(layout) = self
                                .referent(self.operand_ty(operand))
                                .and_then(|t| self.layout(t))
                            && let Some(bytes) = n.scale(layout.size.bytes().into())
                        {
                            out.accesses.insert(Access {
                                argument: p.argument,
                                offset: p.offset,
                                bytes,
                                alignment: layout.align.abi.bytes(),
                                write,
                            });
                        } else {
                            out.unresolved_access = true;
                        }
                    }
                    state.forget_fields();
                }
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let values: Vec<_> = args
                    .iter()
                    .map(|arg| self.operand(&arg.node, &state, out))
                    .collect();
                for arg in args {
                    if let Operand::Move(place) = arg.node {
                        self.invalidate_place(&mut state, place);
                    }
                }
                let targets = match self.operand(func, &state, out) {
                    Some(Value::Functions(targets)) => targets,
                    _ => BTreeSet::new(),
                };
                out.callees.extend(targets.iter().cloned());
                state.locals.remove(&destination.local);
                if !destination.projection.is_empty()
                    || block.terminator().successors().count() != 1
                    || targets.is_empty()
                    || targets.iter().any(|name| !self.summaries.contains_key(name))
                {
                    state.forget_fields();
                    out.unresolved_access = true;
                    return state;
                }
                let mut alternatives = targets.iter().map(|name| {
                    let mut next = state.clone();
                    let summary = &self.summaries[name];
                    if let Some(value) = self.apply_summary(summary, &values, &mut next, out) {
                        next.locals.insert(destination.local, value);
                    }
                    next
                });
                let stride = |local: Local| self.view_stride(self.ty(self.body.local_decls[local].ty));
                if let Some(mut merged) = alternatives.next() {
                    for alternative in alternatives {
                        merged.meet(&alternative, stride);
                    }
                    state = merged;
                }
            }
            TerminatorKind::InlineAsm { options, operands, .. } => {
                for operand in operands {
                    let output = match operand {
                        mir::InlineAsmOperand::Out { place, .. } => *place,
                        mir::InlineAsmOperand::InOut { out_place, .. } => *out_place,
                        _ => None,
                    };
                    if let Some(place) = output {
                        self.invalidate_place(&mut state, place);
                        self.memory(place, &state, true, out);
                    }
                }
                if !options.contains(InlineAsmOptions::NOMEM) {
                    state.forget_fields();
                    out.unresolved_access = true;
                }
            }
            TerminatorKind::Drop { place, .. } => {
                if let Some(Value::Address(p)) = state.locals.remove(&place.local) {
                    Self::forget_root(&mut state, out, p.argument);
                }
                state.forget_fields();
                out.unresolved_access = true;
            }
            _ => {}
        }
        state
    }
}

fn summarize<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
    body: &Body<'tcx>,
    summaries: &BTreeMap<String, Summary>,
) -> Summary {
    let analyzer = Analyzer {
        tcx,
        instance,
        body,
        env: TypingEnv::fully_monomorphized(),
        summaries,
    };
    let mut initial = State::default();
    for (index, local) in body.args_iter().enumerate() {
        let ty = analyzer.ty(body.local_decls[local].ty);
        let value = if let Some(pointee) = analyzer.referent(ty) {
            let length = if matches!(pointee.kind(), ty::Slice(_)) {
                Some(Expr::input(Input::Length(index)))
            } else {
                analyzer.array_length(pointee)
            };
            Some(Value::Address(Pointer {
                argument: index,
                offset: Expr::default(),
                length,
            }))
        } else if crate::word_integer(ty) {
            Some(Value::Scalar(Expr::input(Input::Value(index))))
        } else {
            None
        };
        if let Some(value) = value {
            initial.locals.insert(local, value);
        }
    }
    let stride = |local: Local| analyzer.view_stride(analyzer.ty(body.local_decls[local].ty));
    let mut inputs = BTreeMap::from([(mir::START_BLOCK, Paths::Distinct(vec![initial]))]);
    let mut pending = VecDeque::from([mir::START_BLOCK]);
    while let Some(block) = pending.pop_front() {
        let states: Vec<_> = inputs[&block]
            .states()
            .iter()
            .map(|state| analyzer.transfer(block, state.clone(), &mut Summary::default()))
            .collect();
        for next in body.basic_blocks[block].terminator().successors() {
            let paths = inputs
                .entry(next)
                .or_insert_with(|| Paths::Distinct(Vec::new()));
            let mut changed = false;
            for state in &states {
                changed |= paths.insert(state.clone(), stride);
            }
            if changed {
                pending.push_back(next);
            }
        }
    }
    let mut summary = Summary {
        widened_view_joins: inputs.values().filter(|paths| {
            matches!(paths, Paths::Widened(state) if state.locals.values().any(|value| matches!(value, Value::End(_))))
        }).count(),
        ..Summary::default()
    };
    let mut returns = None::<State>;
    for (block, inputs) in inputs {
        for input in inputs.states() {
            let state = analyzer.transfer(block, input.clone(), &mut summary);
            if matches!(
                body.basic_blocks[block].terminator().kind,
                TerminatorKind::Return
            ) {
                if let Some(result) = &mut returns {
                    result.meet(&state, stride);
                } else {
                    returns = Some(state);
                }
            }
        }
    }
    if let Some(state) = returns {
        let result = state.locals.get(&mir::RETURN_PLACE);
        summary.view_end = stride(mir::RETURN_PLACE).and_then(|stride| result?.view_end(stride));
        match result {
            Some(Value::Address(pointer)) => {
                summary.returned_view = Some(pointer.clone())
            }
            Some(Value::Scalar(value)) => summary.returned_scalar = Some(value.clone()),
            _ => {}
        }
        summary.field_writes = state.fields;
        summary.initialized_words = state.initialized;
    }
    summary
}

pub fn summarize_selected<'tcx>(
    tcx: TyCtxt<'tcx>,
    selected: &BTreeMap<String, Instance<'tcx>>,
) -> BTreeMap<String, Summary> {
    let mut summaries = BTreeMap::new();
    let mut callers = BTreeMap::<&str, BTreeSet<&str>>::new();
    let mut waits: BTreeMap<_, usize> = selected.keys().map(|name| (name.as_str(), 0)).collect();
    for (name, &instance) in selected {
        let body = tcx.instance_mir(instance.def);
        let analyzer = Analyzer {
            tcx,
            instance,
            body,
            env: TypingEnv::fully_monomorphized(),
            summaries: &summaries,
        };
        for block in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &block.terminator().kind
                && let Some(callee) = analyzer.direct_callee(func)
                && let Some((symbol, _)) = selected.get_key_value(tcx.symbol_name(callee).name)
            {
                if callers.entry(symbol).or_default().insert(name) {
                    *waits.get_mut(name.as_str()).expect("selected function") += 1;
                }
            }
        }
    }
    let mut ready: BTreeSet<_> = waits.iter().filter_map(|(&name, &count)| (count == 0).then_some(name)).collect();
    let mut pending = VecDeque::new();
    while let Some(callee) = ready.pop_first() {
        pending.push_back(callee);
        for caller in callers.get(callee).into_iter().flatten() {
            let count = waits.get_mut(caller).expect("selected caller");
            *count -= 1;
            if *count == 0 {
                ready.insert(caller);
            }
        }
    }
    pending.extend(waits.iter().filter_map(|(&name, &count)| (count != 0).then_some(name)));
    let mut queued: BTreeSet<_> = pending.iter().copied().collect();
    let mut updates = BTreeMap::<&str, usize>::new();
    // A recursive access can increase an offset indefinitely. Once a
    // function exceeds the refinement budget, use an unknown-effects summary.
    const MAX_UPDATES: usize = 8;
    while let Some(name) = pending.pop_front() {
        queued.remove(name);
        let count = updates.entry(name).or_default();
        if *count > MAX_UPDATES {
            continue;
        }
        let instance = selected[name];
        let summary = if *count == MAX_UPDATES {
            Summary { unresolved_access: true, ..Summary::default() }
        } else {
            summarize(tcx, instance, tcx.instance_mir(instance.def), &summaries)
        };
        for callee in &summary.callees {
            if let Some((key, _)) = selected.get_key_value(callee) {
                callers.entry(key).or_default().insert(name);
            }
        }
        if summaries.get(name) == Some(&summary) {
            continue;
        }
        *count += 1;
        summaries.insert(name.to_owned(), summary);
        for &caller in callers.get(name).into_iter().flatten() {
            if queued.insert(caller) {
                pending.push_back(caller);
            }
        }
    }
    summaries
}
