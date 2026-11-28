//! Optional Horn reachability refinement for the numerical RV64 projection.
//! Results steer candidate generation. The linked-image checker is authoritative.
use nocompiler_typed::{
    asm::Func,
    cfg::ControlFlow,
    isa::{BrOp, IOp, Instr, ROp, Reg, ShOp, Target, ZERO},
};
use std::{
    collections::BTreeSet,
    fmt::Write as _,
    io::{Read, Seek, Write as _},
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

pub type Edges = BTreeSet<(usize, usize)>;

fn reg(r: Reg) -> String {
    if r == ZERO {
        bv(0)
    } else {
        format!("r{}", r.0)
    }
}

fn bv(n: u64) -> String {
    format!("(_ bv{n} 64)")
}

fn operator(instr: &Instr) -> Option<(&'static str, Reg, Option<Reg>, u64)> {
    match *instr {
        Instr::IOp { op, rs1, imm, .. } => {
            let operation = match op {
                IOp::Addi => "bvadd",
                IOp::Andi => "bvand",
                IOp::Ori => "bvor",
                IOp::Xori => "bvxor",
                _ => return None,
            };
            Some((operation, rs1, None, imm as u64))
        }
        Instr::ROp { op, rs1, rs2, .. } => {
            let operation = match op {
                ROp::Add => "bvadd",
                ROp::Sub => "bvsub",
                ROp::And => "bvand",
                ROp::Or => "bvor",
                ROp::Xor => "bvxor",
                ROp::Mul => "bvmul",
                _ => return None,
            };
            Some((operation, rs1, Some(rs2), 0))
        }
        Instr::Shift { op, rs1, sh, .. } => {
            let operation = match op {
                ShOp::Slli => "bvshl",
                ShOp::Srli => "bvlshr",
                ShOp::Srai => "bvashr",
                _ => return None,
            };
            Some((operation, rs1, None, sh.into()))
        }
        _ => None,
    }
}

fn relation(name: &str, args: impl IntoIterator<Item = String>) -> String {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.is_empty() {
        name.to_owned()
    } else {
        format!("({name} {})", args.join(" "))
    }
}

fn predicate(op: BrOp, a: Reg, b: Reg, taken: bool) -> String {
    let (operation, negate) = match op {
        BrOp::Beq => ("=", false),
        BrOp::Bne => ("=", true),
        BrOp::Blt => ("bvslt", false),
        BrOp::Bge => ("bvslt", true),
        BrOp::Bltu => ("bvult", false),
        BrOp::Bgeu => ("bvult", true),
    };
    let compare = format!("({operation} {} {})", reg(a), reg(b));
    if negate == taken {
        format!("(not {compare})")
    } else {
        compare
    }
}

/// Encode one proof-directed slice projection. Registers outside the
/// projection cannot affect its branch conditions. Unsupported writes are
/// havoced, and all entry registers are initially arbitrary.
fn encode(func: &Func) -> Option<(String, Vec<(usize, usize)>)> {
    if func.instrs.is_empty() || func.instrs.len() > 96 {
        return None;
    }
    let cfg = ControlFlow::new(func);
    let mut relevant = BTreeSet::new();
    let mut branches = Vec::new();
    for &node in &cfg.reverse_postorder {
        if let Instr::Branch {
            op,
            rs1,
            rs2,
            target: Target::Local(target),
        } = func.instrs[node].instr
            && target != node + 1
            && cfg.successors[node].len() == 2
        {
            relevant.extend([rs1, rs2]);
            for &next in &cfg.successors[node] {
                branches.push((node, next, predicate(op, rs1, rs2, next == target)));
            }
        }
    }
    if branches.is_empty() || branches.len() > 12 {
        return None;
    }
    loop {
        let prior = relevant.len();
        for &node in &cfg.reverse_postorder {
            let instr = &func.instrs[node].instr;
            if instr
                .rd()
                .is_some_and(|rd| rd != ZERO && relevant.contains(&rd))
                && let Some((_, src, rhs, _)) = operator(instr)
            {
                relevant.extend(std::iter::once(src).chain(rhs));
            }
        }
        if relevant.len() == prior {
            break;
        }
    }
    relevant.remove(&ZERO);
    if relevant.len() > 12 {
        return None;
    }
    let sorts = vec!["(_ BitVec 64)"; relevant.len()].join(" ");
    let mut program = String::from("(set-logic HORN)\n(set-option :timeout 350)\n");
    for &r in &relevant {
        writeln!(
            program,
            "(declare-var {} (_ BitVec 64))\n(declare-var h{} (_ BitVec 64))",
            reg(r),
            r.0
        )
        .unwrap();
    }
    for &node in &cfg.reverse_postorder {
        writeln!(program, "(declare-rel p{node} ({sorts}))").unwrap();
    }
    let current = |node| relation(&format!("p{node}"), relevant.iter().copied().map(reg));
    writeln!(program, "(rule {})", current(0)).unwrap();
    for &node in &cfg.reverse_postorder {
        let instr = &func.instrs[node].instr;
        let rhs = operator(instr).map(|(op, a, b, imm)| {
            let b = b.map(reg).unwrap_or_else(|| bv(imm));
            format!("({op} {} {b})", reg(a))
        });
        for &next in &cfg.successors[node] {
            let consequent = relation(
                &format!("p{next}"),
                relevant.iter().map(|&r| {
                    if (crate::flow::call(instr).is_some() || matches!(instr, Instr::Ecall))
                        && !r.is_preserved()
                    {
                        format!("h{}", r.0)
                    } else if instr.rd() == Some(r) {
                        rhs.clone().unwrap_or_else(|| {
                            if let Instr::Lui { imm, .. } = *instr {
                                bv(((imm << 12) as i32 as i64) as u64)
                            } else {
                                format!("h{}", r.0)
                            }
                        })
                    } else {
                        reg(r)
                    }
                }),
            );
            let antecedent = match branches.iter().find(|(n, k, _)| (*n, *k) == (node, next)) {
                Some((_, _, compare)) => format!("(and {} {compare})", current(node)),
                None => current(node),
            };
            writeln!(program, "(rule (=> {antecedent} {consequent}))").unwrap();
        }
    }
    let mut queries = Vec::new();
    for (index, (node, next, compare)) in branches.into_iter().enumerate() {
        writeln!(
            program,
            "(declare-rel q{index} ())\n(rule (=> (and {} {compare}) q{index}))",
            current(node)
        )
        .unwrap();
        queries.push((node, next));
    }
    for index in 0..queries.len() {
        writeln!(program, "(query q{index})").unwrap();
    }
    Some((program, queries))
}

fn solve(program: &str, solver: &Path) -> Option<String> {
    let mut input = tempfile::tempfile().ok()?;
    input.write_all(program.as_bytes()).ok()?;
    input.rewind().ok()?;
    let mut output = tempfile::tempfile().ok()?;
    let mut child = Command::new(solver)
        .args(["-in", "-T:3"])
        .stdin(input)
        .stdout(output.try_clone().ok()?)
        .stderr(Stdio::null())
        .spawn()
        .ok()?;
    let deadline = Instant::now() + Duration::from_secs(4);
    let status = loop {
        if let Ok(Some(status)) = child.try_wait() {
            break status;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    if !status.success() || output.metadata().ok()?.len() > 4096 {
        return None;
    }
    output.rewind().ok()?;
    let mut result = String::new();
    output.read_to_string(&mut result).ok()?;
    Some(result)
}

pub fn unreachable(func: &Func, solver: &Path) -> Edges {
    let Some((program, queries)) = encode(func) else {
        return Edges::new();
    };
    let Some(stdout) = solve(&program, solver) else {
        return Edges::new();
    };
    let answers: Vec<_> = stdout.lines().map(str::trim).collect();
    if answers.len() != queries.len()
        || answers
            .iter()
            .any(|answer| !matches!(*answer, "sat" | "unsat" | "unknown"))
    {
        return Edges::new();
    }
    queries
        .into_iter()
        .zip(answers)
        .filter_map(|(edge, answer)| (answer == "unsat").then_some(edge))
        .collect()
}
