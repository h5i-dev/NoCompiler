// Built separately with the pinned rustc-dev toolchain.
#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_target;

mod capture_mir;
#[allow(dead_code)]
mod contract_ir;

use rustc_abi::{BackendRepr, CanonAbi, Primitive};
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::DefKind;
use rustc_interface::interface::Compiler;
use rustc_middle::mir::TerminatorKind;
use rustc_middle::mono::MonoItem;
use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TypingEnv};
use rustc_target::callconv::PassMode;
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::process::ExitCode;

fn word_integer(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::Int(ty::IntTy::I64 | ty::IntTy::Isize) | ty::Uint(ty::UintTy::U64 | ty::UintTy::Usize)
    )
}

fn buffer_element(ty: Ty<'_>) -> bool {
    match ty.kind() {
        ty::Int(_) | ty::Uint(_) => true,
        ty::Array(element, _) => buffer_element(*element),
        _ => false,
    }
}

fn describe_fields<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    prefix: &str,
    offset: u64,
    fields: &mut Vec<String>,
) -> Result<(), String> {
    let env = TypingEnv::fully_monomorphized();
    let layout = tcx
        .layout_of(env.as_query_input(ty))
        .map_err(|error| format!("field layout for {ty}: {error:?}"))?;
    match ty.kind() {
        ty::Adt(def, _) if def.is_struct() => {
            for (index, field) in def.non_enum_variant().fields.iter().enumerate() {
                let name = format!("{prefix}{}", field.name);
                if !name
                    .bytes()
                    .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, b'_' | b'.'))
                {
                    continue;
                }
                let child = layout.field(&ty::layout::LayoutCx::new(tcx, env), index);
                describe_fields(
                    tcx,
                    child.ty,
                    &format!("{name}."),
                    offset + layout.fields.offset(index).bytes(),
                    fields,
                )?;
            }
        }
        ty::Uint(ty::UintTy::U64 | ty::UintTy::Usize)
            if offset % 8 == 0 && layout.size.bytes() == 8 =>
        {
            fields.push(format!("{}@{offset}@word", prefix.trim_end_matches('.')));
        }
        ty::Array(_, count) => {
            if let Some(count) = count.try_to_target_usize(tcx) {
                fields.push(format!("{}@{offset}@{count}", prefix.trim_end_matches('.')));
            }
        }
        _ => {}
    }
    Ok(())
}

fn box_descriptor<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<String> {
    let ty::Adt(def, args) = ty.kind() else {
        return None;
    };
    if Some(def.did()) != tcx.lang_items().owned_box() {
        return None;
    }
    let element = args.type_at(0);
    let allocator = args.type_at(1);
    let ty::Adt(allocator_def, _) = allocator.kind() else {
        return None;
    };
    if qualified_path(tcx, allocator_def.did(), &[]) != "alloc::alloc::Global"
        || !buffer_element(element)
    {
        return None;
    }
    let env = TypingEnv::fully_monomorphized();
    let layout = tcx.layout_of(env.as_query_input(element)).ok()?;
    let size = layout.size.bytes();
    (size > 0).then(|| format!("box:{size}:{}", layout.align.abi.bytes()))
}

fn capture_abi<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> Result<(String, String), String> {
    let name = tcx.symbol_name(instance).name;
    if name.is_empty()
        || !name
            .bytes()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == b'_')
    {
        return Err(format!("unsupported assembly symbol {name}"));
    }

    let typing_env = TypingEnv::fully_monomorphized();
    // Only the integer/pointer register convention is modelled. Pass modes
    // below establish how many consecutive RV64 argument registers each uses.
    let abi = tcx
        .fn_abi_of_instance(typing_env.as_query_input((instance, ty::List::empty())))
        .map_err(|e| format!("could not compute ABI: {e:?}"))?;
    if abi.c_variadic || !matches!(abi.conv, CanonAbi::C | CanonAbi::Rust) {
        return Err("unsupported calling convention".into());
    }
    let word_scalar = |scalar: rustc_abi::Scalar| match scalar.primitive() {
        Primitive::Int(size, _) => size.size().bytes() <= 8,
        Primitive::Pointer(_) => true,
        Primitive::Float(_) => false,
    };
    let output = match abi.ret.mode {
        PassMode::Ignore => "void".into(),
        PassMode::Direct(_) if word_integer(abi.ret.layout.ty) => "word".into(),
        PassMode::Direct(_) if abi.ret.layout.ty.is_box() => box_descriptor(tcx, abi.ret.layout.ty)
            .ok_or_else(|| format!("unsupported Box return type {}", abi.ret.layout.ty))?,
        PassMode::Pair(..)
            if abi.conv == CanonAbi::Rust
                && matches!(
                    abi.ret.layout.backend_repr, BackendRepr::ScalarPair { a, b, .. }
                        if word_scalar(a) && word_scalar(b)
                ) =>
        {
            "pair".into()
        }
        _ => return Err(format!("unsupported return type {}", abi.ret.layout.ty)),
    };

    let mut registers = 0;
    let mut arguments = Vec::new();
    for (index, arg) in abi.args.iter().enumerate() {
        let arg_ty = arg.layout.ty;
        let arg_desc = match (&arg.mode, arg_ty.kind()) {
            (PassMode::Direct(_), ty::Uint(ty::UintTy::U64 | ty::UintTy::Usize)) => "uword".into(),
            (PassMode::Direct(_), _) if word_integer(arg_ty) => "word".into(),
            (PassMode::Direct(_), ty::RawPtr(..)) => "ptr".into(),
            (PassMode::Direct(_), _) if arg_ty.is_box() => box_descriptor(tcx, arg_ty)
                .ok_or_else(|| format!("unsupported Box argument {arg_ty}"))?,
            (mode, ty::Ref(_, pointee, mutability)) => {
                let (element, kind) = match (mode, pointee.kind()) {
                    (PassMode::Pair(..), ty::Slice(element)) => (*element, "slice"),
                    (PassMode::Direct(_), _) => (*pointee, "ref"),
                    _ => return Err(format!("unsupported ABI for argument {index}: {arg_ty}")),
                };
                let aggregate =
                    kind == "ref" && matches!(element.kind(), ty::Adt(def, _) if def.is_struct());
                if (!buffer_element(element) && !aggregate)
                    || (!mutability.is_mut() && !element.is_freeze(tcx, typing_env))
                {
                    return Err(format!(
                        "unsupported referent for argument {index}: {element}"
                    ));
                }
                let layout = tcx
                    .layout_of(typing_env.as_query_input(element))
                    .map_err(|e| format!("could not compute layout of {element}: {e:?}"))?;
                let size = layout.size.bytes();
                let align = layout.align.abi.bytes();
                let permission = if mutability.is_mut() { "rw" } else { "ro" };
                if aggregate {
                    let mut fields = Vec::new();
                    describe_fields(tcx, element, "", 0, &mut fields)?;
                    let ty::Adt(def, _) = element.kind() else {
                        unreachable!()
                    };
                    let type_path = qualified_path(tcx, def.did(), &[]);
                    format!(
                        "struct:{size}:{align}:{permission}:{type_path};{}",
                        fields.join(";")
                    )
                } else {
                    format!("{kind}:{size}:{align}:{permission}")
                }
            }
            _ => return Err(format!("unsupported argument {index}: {arg_ty}")),
        };
        registers += if matches!(arg.mode, PassMode::Pair(..)) {
            2
        } else {
            1
        };
        if registers > 8 {
            return Err("arguments passed on the stack are unsupported".into());
        }
        arguments.push(arg_desc);
    }
    let safety = tcx
        .fn_sig(instance.def_id())
        .instantiate(tcx, instance.args)
        .skip_binder()
        .safety();
    let safety = if safety.is_unsafe() { "unsafe" } else { "safe" };
    Ok((name.into(), format!("{output}\t{}\t{safety}", arguments.join(","))))
}

fn qualified_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: rustc_hir::def_id::DefId,
    args: &'tcx [ty::GenericArg<'tcx>],
) -> String {
    let path = tcx.def_path_str_with_args(def, args);
    let crate_name = tcx.crate_name(def.krate);
    if path.starts_with(&format!("{crate_name}::")) {
        path
    } else {
        format!("{crate_name}::{path}")
    }
}

struct Capture;

impl Callbacks for Capture {
    fn after_analysis<'tcx>(&mut self, _: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let destinations = env::var("NOCOMPILER_CAPTURE_PATH").expect("capture destination");
        let targets = env::var("NOCOMPILER_CAPTURE_TARGETS").expect("capture targets");
        let mut functions = BTreeMap::new();
        for id in tcx.hir_body_owners().map(|id| id.to_def_id()) {
            if matches!(tcx.def_kind(id), DefKind::Fn | DefKind::AssocFn)
                && tcx.generics_of(id).count() == 0
            {
                functions.insert(qualified_path(tcx, id, &[]), Some(Instance::mono(tcx, id)));
            }
        }
        let targets: Vec<_> = targets.lines().collect();
        let mut instances = BTreeSet::new();
        for cgu in tcx.collect_and_partition_mono_items(()).codegen_units {
            for item in cgu.items().keys() {
                let MonoItem::Fn(instance) = *item else {
                    continue;
                };
                let name = tcx.symbol_name(instance).name;
                let path = qualified_path(tcx, instance.def_id(), instance.args);
                let bare = qualified_path(tcx, instance.def_id(), &[]);
                instances.insert(format!("{path}\t{name}"));
                for key in [name, path.as_str(), bare.as_str()] {
                    if targets.contains(&key) {
                        functions
                            .entry(key.to_owned())
                            .and_modify(|existing| {
                                if existing.is_some_and(|previous| previous != instance) {
                                    *existing = None;
                                }
                            })
                            .or_insert(Some(instance));
                    }
                }
            }
        }
        let mut layouts = String::new();
        let mut diagnostics = String::new();
        let mut inlining = String::new();
        let mut calls = String::new();
        let mut selected_mir = BTreeMap::new();
        for path in targets {
            let instance = match functions.get(path) {
                Some(&Some(def)) => def,
                Some(None) => {
                    diagnostics.push_str(&format!("{path}\tfunction path is ambiguous\n"));
                    continue;
                }
                None => {
                    diagnostics.push_str(&format!(
                        "{path}\tfunction was not found in the selected Cargo binary\n"
                    ));
                    continue;
                }
            };
            match capture_abi(tcx, instance) {
                Ok((name, layout)) => {
                    layouts.push_str(&format!("{path}\t{name}\t{layout}\n"));
                    if tcx.is_mir_available(instance.def_id()) {
                        let body = tcx.instance_mir(instance.def);
                        selected_mir.insert(name.clone(), instance);
                        let callees: BTreeSet<_> = body
                            .source_scopes
                            .iter()
                            .filter_map(|scope| scope.inlined)
                            .map(|(callee, _)| qualified_path(tcx, callee.def_id(), callee.args))
                            .collect();
                        for callee in callees {
                            inlining.push_str(&format!("{path}\t{callee}\n"));
                        }
                        let direct: BTreeSet<_> = body
                            .basic_blocks
                            .iter()
                            .filter_map(|block| match &block.terminator().kind {
                                TerminatorKind::Call { func, .. } => {
                                    match *func.ty(&body.local_decls, tcx).kind() {
                                        ty::FnDef(def, args) => {
                                            Some(qualified_path(tcx, def, args.skip_binder()))
                                        }
                                        _ => None,
                                    }
                                }
                                _ => None,
                            })
                            .collect();
                        for callee in direct {
                            calls.push_str(&format!("{path}\t{callee}\n"));
                        }
                    }
                }
                Err(error) => {
                    let error = error.replace(['\t', '\r', '\n'], " ");
                    diagnostics.push_str(&format!("{path}\t{error}\n"));
                }
            }
        }
        let mut summaries = String::new();
        for (name, summary) in capture_mir::summarize_selected(tcx, &selected_mir) {
            summary.encode(&name, &mut summaries);
        }
        let result = std::fs::write(format!("{destinations}/abi.tsv"), layouts)
            .and_then(|()| std::fs::write(format!("{destinations}/mir-contracts.tsv"), summaries))
            .and_then(|()| std::fs::write(format!("{destinations}/unsupported.tsv"), diagnostics))
            .and_then(|()| std::fs::write(format!("{destinations}/inlined.tsv"), inlining))
            .and_then(|()| std::fs::write(format!("{destinations}/mir-calls.tsv"), calls))
            .and_then(|()| {
                std::fs::write(
                    format!("{destinations}/instances.tsv"),
                    instances.into_iter().collect::<Vec<_>>().join("\n"),
                )
            });
        if let Err(error) = result {
            tcx.dcx()
                .err(format!("NoCompiler: could not write annotations: {error}"));
        }
        Compilation::Continue
    }
}

fn main() -> ExitCode {
    let mut args: Vec<_> = env::args().skip(1).collect();
    if let Some(index) = args.iter().position(|arg| arg == "--nocompiler-capture") {
        args.remove(index);
        args.extend([
            "--sysroot".into(),
            env::var("NOCOMPILER_RUST_SYSROOT").expect("rustc sysroot"),
        ]);
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Capture))
    } else {
        use std::os::unix::process::CommandExt;
        let error = std::process::Command::new(&args[0]).args(&args[1..]).exec();
        eprintln!("cannot run {}: {error}", args[0]);
        ExitCode::FAILURE
    }
}
