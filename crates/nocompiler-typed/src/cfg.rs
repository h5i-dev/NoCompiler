//! Static control flow shared by the checker and annotation inference.
use crate::{
    asm::Func,
    isa::{Instr, Target, ZERO},
};
use std::collections::{BTreeMap, BTreeSet};

/// Static successors, in instruction indices. An empty list leaves the function.
pub fn static_successors(i: &Instr, ix: usize) -> Vec<usize> {
    let next = ix + 1;
    match i {
        Instr::Branch {
            target: Target::Local(t),
            ..
        } => vec![*t, next],
        Instr::Jal {
            rd,
            target: Target::Local(t),
        } if *rd == ZERO => vec![*t],
        Instr::Jal { rd, .. } | Instr::CallPair { rd, .. } if *rd == ZERO => vec![],
        Instr::Jalr { .. } | Instr::Unimp => vec![],
        Instr::Ecall => vec![next],
        _ => vec![next],
    }
}

/// Reachable control flow and dominator back edges, in reverse postorder.
pub struct ControlFlow {
    pub successors: Vec<Vec<usize>>,
    pub predecessors: Vec<Vec<usize>>,
    pub reverse_postorder: Vec<usize>,
    pub back_edges: Vec<(usize, usize)>,
}

impl ControlFlow {
    pub fn new(function: &Func) -> Self {
        let n = function.instrs.len();
        if n == 0 {
            return Self {
                successors: vec![],
                predecessors: vec![],
                reverse_postorder: vec![],
                back_edges: vec![],
            };
        }
        let succ: Vec<Vec<usize>> = (0..n)
            .map(|i| {
                static_successors(&function.instrs[i].instr, i)
                    .into_iter()
                    .filter(|t| *t < n)
                    .collect()
            })
            .collect();
        // reverse postorder from the entry
        let mut post = Vec::new();
        let mut seen = vec![false; n];
        let mut stack = vec![(0, 0)];
        seen[0] = true;
        while let Some((u, k)) = stack.pop() {
            if k < succ[u].len() {
                stack.push((u, k + 1));
                let v = succ[u][k];
                if !seen[v] {
                    seen[v] = true;
                    stack.push((v, 0));
                }
            } else {
                post.push(u);
            }
        }
        let rpo: Vec<usize> = post.iter().rev().copied().collect();
        let mut num = vec![usize::MAX; n];
        for (i, u) in rpo.iter().enumerate() {
            num[*u] = i;
        }
        let mut preds: Vec<Vec<usize>> = vec![vec![]; n];
        for u in 0..n {
            if seen[u] {
                for &v in &succ[u] {
                    preds[v].push(u);
                }
            }
        }
        // dominators (Cooper, Harvey, Kennedy)
        let mut idom = vec![usize::MAX; n];
        idom[0] = 0;
        let intersect = |idom: &Vec<usize>, mut a: usize, mut b: usize| {
            while a != b {
                while num[a] > num[b] {
                    a = idom[a];
                }
                while num[b] > num[a] {
                    b = idom[b];
                }
            }
            a
        };
        let mut changed = true;
        while changed {
            changed = false;
            for &u in rpo.iter().skip(1) {
                let mut new = usize::MAX;
                for &p in &preds[u] {
                    if idom[p] != usize::MAX {
                        new = if new == usize::MAX {
                            p
                        } else {
                            intersect(&idom, p, new)
                        };
                    }
                }
                if new != idom[u] {
                    idom[u] = new;
                    changed = true;
                }
            }
        }
        let dominates = |h: usize, mut u: usize| loop {
            if u == h {
                return true;
            }
            if u == 0 || idom[u] == usize::MAX {
                return false;
            }
            u = idom[u];
        };

        let back_edges = rpo
            .iter()
            .flat_map(|&u| succ[u].iter().copied().map(move |t| (u, t)))
            .filter(|&(u, t)| dominates(t, u))
            .collect();
        Self {
            successors: succ,
            predecessors: preds,
            reverse_postorder: rpo,
            back_edges,
        }
    }
}

/// Natural loop bodies, grouped by dominating header.
pub fn loop_bodies<'a>(
    predecessors: &[Vec<usize>],
    back_edges: impl IntoIterator<Item = &'a (usize, usize)>,
) -> BTreeMap<usize, BTreeSet<usize>> {
    let mut bodies = BTreeMap::new();
    for &(u, h) in back_edges {
        let body = bodies.entry(h).or_insert_with(|| BTreeSet::from([h]));
        let mut work = vec![u];
        while let Some(node) = work.pop() {
            if body.insert(node) {
                work.extend(predecessors[node].iter().copied());
            }
        }
    }
    bodies
}
