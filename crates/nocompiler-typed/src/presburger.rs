//! A decision procedure for quantifier-free Presburger arithmetic (decision I1 in
//! docs/typed/decisions.md).
//!
//! `prove(hyps, goal)` answers whether every integer valuation satisfying all `hyps`
//! satisfies `goal`. It refutes `hyps ∧ ¬goal`:
//!
//! 1. negation normal form, with `¬(e ≥ 0)` as `−e − 1 ≥ 0`, `¬(e = 0)` as a disjunction
//!    of two inequalities and `¬(c ∣ e)` kept as an atom;
//! 2. a depth-first search over the disjunctions (lazy DNF), refuting each conjunction;
//! 3. per conjunction, `c ∣ e` becomes `e = c·q` and `¬(c ∣ e)` becomes `e = c·q + r`,
//!    `1 ≤ r ≤ c − 1`, with fresh `q`, `r`;
//! 4. the Omega test (Pugh 1991): equalities are eliminated exactly (a unimodular change
//!    of variables when no coefficient is ±1), then variables are eliminated from the
//!    inequalities by Fourier–Motzkin, exactly when a unit coefficient allows it, and
//!    otherwise with the real shadow, the dark shadow and the splinters.
//!
//! Every answer other than "proved" is "not proved": a satisfiable conjunction, an `i128`
//! overflow, or a spent budget. So an overflow or a budget can only make the checker
//! reject, never accept.

use crate::formula::Formula;
use crate::lin::{Lin, Var, floor_div, gcd};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    /// The goal follows from the hypotheses.
    Proved,
    /// A conjunction of the negated goal and the hypotheses is satisfiable.
    Refuted,
    /// Overflow or budget: nothing is known.
    Unknown,
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Sat {
    Sat,
    Unsat,
    Unknown,
}

/// Atoms of the negation normal form.
#[derive(Clone, Debug)]
enum Atom {
    Ge(Lin),
    Eq(Lin),
    Dvd(i128, Lin),
    NDvd(i128, Lin),
}

#[derive(Clone, Debug)]
enum Nnf {
    T,
    F,
    Atom(Atom),
    And(Vec<Nnf>),
    Or(Vec<Nnf>),
}

fn nnf(f: &Formula, pos: bool) -> Option<Nnf> {
    Some(match (f, pos) {
        (Formula::True, true) | (Formula::False, false) => Nnf::T,
        (Formula::True, false) | (Formula::False, true) => Nnf::F,
        (Formula::Ge(e), true) => Nnf::Atom(Atom::Ge(e.clone())),
        (Formula::Ge(e), false) => Nnf::Atom(Atom::Ge(e.scale(-1)?.add_const(-1)?)),
        (Formula::Eq(e), true) => Nnf::Atom(Atom::Eq(e.clone())),
        (Formula::Eq(e), false) => Nnf::Or(vec![
            Nnf::Atom(Atom::Ge(e.add_const(-1)?)),
            Nnf::Atom(Atom::Ge(e.scale(-1)?.add_const(-1)?)),
        ]),
        (Formula::Dvd(c, e), true) => Nnf::Atom(Atom::Dvd(*c, e.clone())),
        (Formula::Dvd(c, e), false) => Nnf::Atom(Atom::NDvd(*c, e.clone())),
        (Formula::And(fs), true) | (Formula::Or(fs), false) => {
            Nnf::And(fs.iter().map(|g| nnf(g, pos)).collect::<Option<_>>()?)
        }
        (Formula::Or(fs), true) | (Formula::And(fs), false) => {
            Nnf::Or(fs.iter().map(|g| nnf(g, pos)).collect::<Option<_>>()?)
        }
        (Formula::Not(g), p) => nnf(g, !p)?,
    })
}

/// Limits that bound the work on one query.
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    /// Constraints produced by eliminations, over the whole query.
    pub constraints: usize,
    /// Leaves of the disjunction search.
    pub leaves: usize,
    /// Splinters tried at one elimination step.
    pub splinters: i128,
}

impl Default for Budget {
    fn default() -> Self {
        Budget {
            constraints: 200_000,
            leaves: 4096,
            splinters: 64,
        }
    }
}

struct Solver {
    next: u32,
    budget: Budget,
    used_constraints: usize,
    used_leaves: usize,
}

/// Decides `hyps ⊢ goal`. Hypotheses that share no variable with the goal (directly or
/// through other hypotheses) are left out first; dropping hypotheses is sound.
pub fn prove(hyps: &[Formula], goal: &Formula) -> Verdict {
    prove_with(hyps, goal, Budget::default())
}

pub fn prove_with(hyps: &[Formula], goal: &Formula, budget: Budget) -> Verdict {
    let rel = relevant(hyps, goal);
    let mut max = 0u32;
    let mut vs = BTreeSet::new();
    goal.vars(&mut vs);
    for h in &rel {
        h.vars(&mut vs);
    }
    if let Some(v) = vs.iter().next_back() {
        max = v.0 + 1;
    }
    let mut parts = Vec::with_capacity(rel.len() + 1);
    for h in &rel {
        match nnf(h, true) {
            Some(n) => parts.push(n),
            None => return Verdict::Unknown,
        }
    }
    match nnf(goal, false) {
        Some(n) => parts.push(n),
        None => return Verdict::Unknown,
    }
    let mut s = Solver {
        next: max,
        budget,
        used_constraints: 0,
        used_leaves: 0,
    };
    match s.search(Vec::new(), parts) {
        Sat::Unsat => Verdict::Proved,
        Sat::Sat => Verdict::Refuted,
        Sat::Unknown => Verdict::Unknown,
    }
}

/// The hypotheses connected to the goal's variables. Variable-free hypotheses are kept
/// (a false one proves everything; a true one costs nothing).
fn relevant<'a>(hyps: &'a [Formula], goal: &Formula) -> Vec<&'a Formula> {
    let hv: Vec<BTreeSet<Var>> = hyps
        .iter()
        .map(|h| {
            let mut s = BTreeSet::new();
            h.vars(&mut s);
            s
        })
        .collect();
    let mut reach = BTreeSet::new();
    goal.vars(&mut reach);
    if reach.is_empty() {
        // A variable-free goal (`false`): every hypothesis may matter.
        return hyps.iter().collect();
    }
    let mut taken = vec![false; hyps.len()];
    loop {
        let mut changed = false;
        for (i, s) in hv.iter().enumerate() {
            if !taken[i] && (s.is_empty() || !s.is_disjoint(&reach)) {
                taken[i] = true;
                reach.extend(s.iter().copied());
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    hyps.iter()
        .zip(taken)
        .filter(|(_, t)| *t)
        .map(|(h, _)| h)
        .collect()
}

fn round_div(a: i128, b: i128) -> Option<i128> {
    // nearest integer to a/b
    let (a, b) = if b < 0 {
        (a.checked_neg()?, b.checked_neg()?)
    } else {
        (a, b)
    };
    Some(floor_div(
        a.checked_mul(2)?.checked_add(b)?,
        b.checked_mul(2)?,
    ))
}

impl Solver {
    fn fresh(&mut self) -> Var {
        self.next += 1;
        Var(self.next - 1)
    }

    fn search(&mut self, mut conj: Vec<Atom>, mut pending: Vec<Nnf>) -> Sat {
        let mut ors = Vec::new();
        while let Some(p) = pending.pop() {
            match p {
                Nnf::T => {}
                Nnf::F => return Sat::Unsat,
                Nnf::Atom(a) => conj.push(a),
                Nnf::And(v) => pending.extend(v),
                Nnf::Or(v) => ors.push(v),
            }
        }
        let here = self.conj(&conj);
        if here == Sat::Unsat || ors.is_empty() {
            if ors.is_empty() {
                self.used_leaves += 1;
            }
            return here;
        }
        if self.used_leaves > self.budget.leaves {
            return Sat::Unknown;
        }
        let first = ors.remove(0);
        let rest: Vec<Nnf> = ors.into_iter().map(Nnf::Or).collect();
        let mut result = Sat::Unsat;
        for branch in first {
            let mut p = rest.clone();
            p.push(branch);
            match self.search(conj.clone(), p) {
                Sat::Unsat => {}
                Sat::Sat => return Sat::Sat,
                Sat::Unknown => result = Sat::Unknown,
            }
        }
        result
    }

    fn conj(&mut self, atoms: &[Atom]) -> Sat {
        let mut eqs = Vec::new();
        let mut ges = Vec::new();
        for a in atoms {
            let r = (|| -> Option<bool> {
                match a {
                    Atom::Ge(e) => ges.push(e.clone()),
                    Atom::Eq(e) => eqs.push(e.clone()),
                    Atom::Dvd(c, e) => {
                        if *c <= 0 {
                            return None;
                        }
                        if *c != 1 {
                            let q = self.fresh();
                            let mut e = e.clone();
                            e.add_term(q, c.checked_neg()?)?;
                            eqs.push(e);
                        }
                    }
                    Atom::NDvd(c, e) => {
                        if *c <= 0 {
                            return None;
                        }
                        if *c == 1 {
                            return Some(false);
                        }
                        let q = self.fresh();
                        let r = self.fresh();
                        let mut e = e.clone();
                        e.add_term(q, c.checked_neg()?)?;
                        e.add_term(r, -1)?;
                        eqs.push(e);
                        ges.push(Lin::var(r).add_const(-1)?);
                        ges.push(Lin::var(r).scale(-1)?.add_const(c - 1)?);
                    }
                }
                Some(true)
            })();
            match r {
                None => return Sat::Unknown,
                Some(false) => return Sat::Unsat,
                Some(true) => {}
            }
        }
        self.omega(eqs, ges)
    }

    fn charge(&mut self, n: usize) -> bool {
        self.used_constraints += n;
        self.used_constraints <= self.budget.constraints
    }

    /// Satisfiability of `eqs = 0 ∧ ges ≥ 0` over the integers.
    fn omega(&mut self, mut eqs: Vec<Lin>, mut ges: Vec<Lin>) -> Sat {
        loop {
            // Normalise the equalities.
            let mut norm = Vec::with_capacity(eqs.len());
            for e in eqs.drain(..) {
                if e.is_const() {
                    if e.konst != 0 {
                        return Sat::Unsat;
                    }
                    continue;
                }
                let g = e.coef_gcd();
                if e.konst % g != 0 {
                    return Sat::Unsat;
                }
                let mut d = e;
                if g != 1 {
                    for c in d.terms.values_mut() {
                        *c /= g;
                    }
                    d.konst /= g;
                }
                norm.push(d);
            }
            eqs = norm;
            if eqs.is_empty() {
                break;
            }
            // The equality and variable with the smallest coefficient.
            let (ei, x, a) = {
                let mut best: Option<(usize, Var, i128)> = None;
                for (i, e) in eqs.iter().enumerate() {
                    for (v, c) in &e.terms {
                        if best.is_none_or(|(_, _, b)| c.unsigned_abs() < b.unsigned_abs()) {
                            best = Some((i, *v, *c));
                        }
                    }
                }
                best.unwrap()
            };
            let sub = if a.abs() == 1 {
                // a·x + r = 0  ⇒  x = −a·r
                let e = eqs.swap_remove(ei);
                let mut r = e;
                r.terms.remove(&x);
                match r.scale(-a) {
                    Some(s) => s,
                    None => return Sat::Unknown,
                }
            } else {
                // x = σ − Σ round(a_y/a)·y − round(c/a): the equality's other
                // coefficients become at most |a|/2.
                let e = &eqs[ei];
                let sigma = self.fresh();
                let mut s = Lin::var(sigma);
                for (y, c) in &e.terms {
                    if *y == x {
                        continue;
                    }
                    let Some(q) = round_div(*c, a) else {
                        return Sat::Unknown;
                    };
                    if s.add_term(*y, -q).is_none() {
                        return Sat::Unknown;
                    }
                }
                let Some(qc) = round_div(e.konst, a) else {
                    return Sat::Unknown;
                };
                match s.add_const(-qc) {
                    Some(s) => s,
                    None => return Sat::Unknown,
                }
            };
            if !self.charge(eqs.len() + ges.len()) {
                return Sat::Unknown;
            }
            for e in eqs.iter_mut().chain(ges.iter_mut()) {
                match e.subst(x, &sub) {
                    Some(n) => *e = n,
                    None => return Sat::Unknown,
                }
            }
        }
        self.ineqs(ges)
    }

    fn ineqs(&mut self, ges: Vec<Lin>) -> Sat {
        // Normalise, keep the tightest constant per linear part.
        let mut by_terms: BTreeMap<BTreeMap<Var, i128>, i128> = BTreeMap::new();
        for e in ges {
            if e.is_const() {
                if e.konst < 0 {
                    return Sat::Unsat;
                }
                continue;
            }
            let g = e.coef_gcd();
            let mut terms = e.terms;
            if g != 1 {
                for c in terms.values_mut() {
                    *c /= g;
                }
            }
            let k = floor_div(e.konst, g);
            by_terms
                .entry(terms)
                .and_modify(|c| *c = (*c).min(k))
                .or_insert(k);
        }
        // Opposite pairs: t + c1 ≥ 0 and −t + c2 ≥ 0.
        for (t, c1) in &by_terms {
            let neg: BTreeMap<Var, i128> = t.iter().map(|(v, c)| (*v, -*c)).collect();
            if let Some(c2) = by_terms.get(&neg) {
                let Some(s) = c1.checked_add(*c2) else {
                    return Sat::Unknown;
                };
                if s < 0 {
                    return Sat::Unsat;
                }
                if s == 0 {
                    let eq = Lin {
                        terms: t.clone(),
                        konst: *c1,
                    };
                    let rest: Vec<Lin> = by_terms
                        .iter()
                        .map(|(t, c)| Lin {
                            terms: t.clone(),
                            konst: *c,
                        })
                        .collect();
                    return self.omega(vec![eq], rest);
                }
            }
        }
        let ges: Vec<Lin> = by_terms
            .into_iter()
            .map(|(terms, konst)| Lin { terms, konst })
            .collect();
        if ges.is_empty() {
            return Sat::Sat;
        }
        // Choose the variable to eliminate.
        let mut vars: BTreeMap<Var, (usize, usize, bool, bool)> = BTreeMap::new();
        for e in &ges {
            for (v, c) in &e.terms {
                let ent = vars.entry(*v).or_insert((0, 0, true, true));
                if *c > 0 {
                    ent.0 += 1;
                    ent.2 &= *c == 1;
                } else {
                    ent.1 += 1;
                    ent.3 &= *c == -1;
                }
            }
        }
        if let Some((&x, _)) = vars.iter().find(|(_, (l, u, _, _))| *l == 0 || *u == 0) {
            let rest: Vec<Lin> = ges.into_iter().filter(|e| e.coef(x) == 0).collect();
            return self.ineqs(rest);
        }
        let score = |(l, u, _, _): &(usize, usize, bool, bool)| l * u;
        let exact = vars
            .iter()
            .filter(|(_, s)| s.2 || s.3)
            .min_by_key(|(_, s)| score(s));
        let (x, is_exact) = match exact {
            Some((v, _)) => (*v, true),
            None => (*vars.iter().min_by_key(|(_, s)| score(s)).unwrap().0, false),
        };
        let (mut lows, mut ups, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for e in &ges {
            let c = e.coef(x);
            if c > 0 {
                lows.push(e.clone());
            } else if c < 0 {
                ups.push(e.clone());
            } else {
                rest.push(e.clone());
            }
        }
        if !self.charge(lows.len() * ups.len()) {
            return Sat::Unknown;
        }
        let mut real = rest.clone();
        let mut dark = rest;
        for lo in &lows {
            let b = lo.coef(x);
            let mut l = lo.clone();
            l.terms.remove(&x);
            for up in &ups {
                let a = -up.coef(x);
                let mut u = up.clone();
                u.terms.remove(&x);
                let g = gcd(a, b);
                // a·L + b·U ≥ 0 (real shadow), divided by gcd(a, b)
                let Some(r) = l.scale(a / g).and_then(|p| p.add(&u.scale(b / g)?)) else {
                    return Sat::Unknown;
                };
                real.push(r);
                if !is_exact {
                    let Some(d) = l
                        .scale(a)
                        .and_then(|p| p.add(&u.scale(b)?))
                        .and_then(|p| p.add_const(-((a - 1).checked_mul(b - 1)?)))
                    else {
                        return Sat::Unknown;
                    };
                    dark.push(d);
                }
            }
        }
        if is_exact {
            return self.ineqs(real);
        }
        match self.ineqs(real) {
            Sat::Unsat => return Sat::Unsat,
            Sat::Unknown => return Sat::Unknown,
            Sat::Sat => {}
        }
        let dark_r = self.ineqs(dark);
        if dark_r == Sat::Sat {
            return Sat::Sat;
        }
        // Splinters: some lower bound b·x ≥ −L is met within (a_max·b − a_max − b)/a_max.
        let a_max = ups.iter().map(|u| -u.coef(x)).max().unwrap();
        let mut result = dark_r;
        for lo in &lows {
            let b = lo.coef(x);
            let Some(top) = a_max.checked_mul(b).and_then(|p| p.checked_sub(a_max + b)) else {
                return Sat::Unknown;
            };
            let top = floor_div(top, a_max);
            if top + 1 > self.budget.splinters {
                return Sat::Unknown;
            }
            for i in 0..=top {
                let Some(eq) = lo.add_const(-i) else {
                    return Sat::Unknown;
                };
                match self.omega(vec![eq], ges.clone()) {
                    Sat::Sat => return Sat::Sat,
                    Sat::Unknown => result = Sat::Unknown,
                    Sat::Unsat => {}
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lin::{Names, TWO64};

    fn v(x: Var) -> Lin {
        Lin::var(x)
    }
    fn k(c: i128) -> Lin {
        Lin::konst(c)
    }
    fn le(a: Lin, b: Lin) -> Formula {
        Formula::le(&a, &b).unwrap()
    }
    fn lt(a: Lin, b: Lin) -> Formula {
        Formula::lt(&a, &b).unwrap()
    }

    #[test]
    fn trivial() {
        assert_eq!(prove(&[], &Formula::True), Verdict::Proved);
        assert_eq!(prove(&[], &Formula::False), Verdict::Refuted);
        assert_eq!(prove(&[Formula::False], &Formula::False), Verdict::Proved);
    }

    #[test]
    fn transitivity_and_integrality() {
        let mut n = Names::default();
        let x = n.fresh("x");
        let y = n.fresh("y");
        // x < y ⊢ x + 1 ≤ y (integers)
        assert_eq!(
            prove(&[lt(v(x), v(y))], &le(v(x).add_const(1).unwrap(), v(y))),
            Verdict::Proved
        );
        // 2x = 2y + 1 is unsatisfiable
        let h = Formula::eq(
            &v(x).scale(2).unwrap(),
            &v(y).scale(2).unwrap().add_const(1).unwrap(),
        )
        .unwrap();
        assert_eq!(prove(&[h], &Formula::False), Verdict::Proved);
        // 1 ≤ 3x ≤ 2 has no integer solution (needs the dark shadow / splinters)
        let h1 = le(k(1), v(x).scale(3).unwrap());
        let h2 = le(v(x).scale(3).unwrap(), k(2));
        assert_eq!(prove(&[h1, h2], &Formula::False), Verdict::Proved);
        // x ≤ 5 does not give x ≤ 4
        assert_eq!(prove(&[le(v(x), k(5))], &le(v(x), k(4))), Verdict::Refuted);
    }

    #[test]
    fn pugh_example_needs_splinters() {
        // 27 ≤ 11x + 13y ≤ 45, −10 ≤ 7x − 9y ≤ 4 has no integer solution (Pugh 1991).
        let mut n = Names::default();
        let x = n.fresh("x");
        let y = n.fresh("y");
        let s = v(x)
            .scale(11)
            .unwrap()
            .add(&v(y).scale(13).unwrap())
            .unwrap();
        let d = v(x).scale(7).unwrap().sub(&v(y).scale(9).unwrap()).unwrap();
        let hyps = [
            le(k(27), s.clone()),
            le(s, k(45)),
            le(k(-10), d.clone()),
            le(d, k(4)),
        ];
        assert_eq!(prove(&hyps, &Formula::False), Verdict::Proved);
        // and with the bound relaxed there is one: x = 3, y = 1 gives 46 and 12.
        let s = v(x)
            .scale(11)
            .unwrap()
            .add(&v(y).scale(13).unwrap())
            .unwrap();
        let d = v(x).scale(7).unwrap().sub(&v(y).scale(9).unwrap()).unwrap();
        let hyps = [
            le(k(27), s.clone()),
            le(s, k(46)),
            le(k(-10), d.clone()),
            le(d, k(12)),
        ];
        assert_eq!(prove(&hyps, &Formula::False), Verdict::Refuted);
    }

    #[test]
    fn divisibility() {
        let mut n = Names::default();
        let r = n.fresh("r");
        let m = n.fresh("m");
        let nn = n.fresh("n");
        // 8 | r ⊢ 8 | r + 8n − 8m
        let a = v(r)
            .add(&v(nn).scale(8).unwrap())
            .unwrap()
            .sub(&v(m).scale(8).unwrap())
            .unwrap();
        assert_eq!(
            prove(&[Formula::Dvd(8, v(r))], &Formula::Dvd(8, a.clone())),
            Verdict::Proved
        );
        assert_eq!(
            prove(&[Formula::Dvd(4, v(r))], &Formula::Dvd(8, a)),
            Verdict::Refuted
        );
    }

    #[test]
    fn sum_example_wraparound() {
        // ¬(2^64 | n), 0 ≤ n < 2^64 ⊢ n ≥ 1
        let mut n = Names::default();
        let x = n.fresh("n");
        let hyps = [
            Formula::negate(Formula::Dvd(TWO64, v(x))),
            Formula::in_u64(&v(x)).unwrap(),
        ];
        assert_eq!(prove(&hyps, &le(k(1), v(x))), Verdict::Proved);
        // 2^64 | n, 0 ≤ n < 2^64 ⊢ n = 0
        let hyps = [Formula::Dvd(TWO64, v(x)), Formula::in_u64(&v(x)).unwrap()];
        assert_eq!(
            prove(&hyps, &Formula::eq(&v(x), &k(0)).unwrap()),
            Verdict::Proved
        );
        // without the range it does not follow
        assert_eq!(
            prove(
                &[Formula::Dvd(TWO64, v(x))],
                &Formula::eq(&v(x), &k(0)).unwrap()
            ),
            Verdict::Refuted
        );
    }

    #[test]
    fn capability_bounds() {
        // 0 ≤ 8n, ρ + 8n ≤ 2^64, 0 ≤ ρ  ⊢  n < 2^64
        let mut n = Names::default();
        let r = n.fresh("rho");
        let x = n.fresh("n");
        let hyps = [
            le(k(0), v(x).scale(8).unwrap()),
            le(v(r).add(&v(x).scale(8).unwrap()).unwrap(), k(TWO64)),
            le(k(0), v(r)),
        ];
        assert_eq!(prove(&hyps, &lt(v(x), k(TWO64))), Verdict::Proved);
        assert_eq!(prove(&hyps, &lt(v(x), k(TWO64 / 8))), Verdict::Refuted);
        assert_eq!(prove(&hyps, &le(v(x), k(TWO64 / 8))), Verdict::Proved);
    }

    #[test]
    fn disjunctions() {
        let mut n = Names::default();
        let x = n.fresh("x");
        // (x = 1 ∨ x = 2) ⊢ 1 ≤ x ≤ 2
        let h = Formula::or(vec![
            Formula::eq(&v(x), &k(1)).unwrap(),
            Formula::eq(&v(x), &k(2)).unwrap(),
        ]);
        let g = Formula::and(vec![le(k(1), v(x)), le(v(x), k(2))]);
        assert_eq!(prove(std::slice::from_ref(&h), &g), Verdict::Proved);
        // ⊬ x = 1
        assert_eq!(
            prove(&[h], &Formula::eq(&v(x), &k(1)).unwrap()),
            Verdict::Refuted
        );
        // x ≠ 0, 0 ≤ x ≤ 1 ⊢ x = 1
        let hyps = [
            Formula::negate(Formula::eq(&v(x), &k(0)).unwrap()),
            le(k(0), v(x)),
            le(v(x), k(1)),
        ];
        assert_eq!(
            prove(&hyps, &Formula::eq(&v(x), &k(1)).unwrap()),
            Verdict::Proved
        );
    }

    #[test]
    fn unsigned_representative() {
        // e = x + 2^64 k, 0 ≤ x < 2^64, 0 ≤ e < 2^64 ⊢ x = e
        let mut n = Names::default();
        let e = n.fresh("e");
        let x = n.fresh("x");
        let kk = n.fresh("k");
        let hyps = [
            Formula::eq(&v(e), &v(x).add(&v(kk).scale(TWO64).unwrap()).unwrap()).unwrap(),
            Formula::in_u64(&v(x)).unwrap(),
            Formula::in_u64(&v(e)).unwrap(),
        ];
        assert_eq!(
            prove(&hyps, &Formula::eq(&v(x), &v(e)).unwrap()),
            Verdict::Proved
        );
        // with e only signed-ranged, x = e + 2^64 when e < 0
        let hyps = [
            Formula::eq(&v(e), &v(x).add(&v(kk).scale(TWO64).unwrap()).unwrap()).unwrap(),
            Formula::in_u64(&v(x)).unwrap(),
            le(k(-5), v(e)),
            lt(v(e), k(0)),
        ];
        assert_eq!(
            prove(
                &hyps,
                &Formula::eq(&v(x), &v(e).add_const(TWO64).unwrap()).unwrap()
            ),
            Verdict::Proved
        );
    }

    /// Brute force on small boxes against the procedure.
    #[test]
    fn random_against_brute_force() {
        let mut seed: u64 = 0x9e3779b97f4a7c15;
        let mut rnd = |m: i128| -> i128 {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            (seed % (2 * m as u64 + 1)) as i128 - m
        };
        let mut n = Names::default();
        let x = n.fresh("x");
        let y = n.fresh("y");
        let z = n.fresh("z");
        let vars = [x, y, z];
        for _ in 0..400 {
            let mut fs = Vec::new();
            // box −6..6 on all variables so brute force is exact
            for &w in &vars {
                fs.push(le(k(-6), v(w)));
                fs.push(le(v(w), k(6)));
            }
            let natoms = 1 + rnd(2).unsigned_abs() as usize;
            for _ in 0..natoms {
                let mut e = Lin::konst(rnd(8));
                for &w in &vars {
                    e.add_term(w, rnd(4)).unwrap();
                }
                let f = match rnd(3) {
                    -3 | -2 => Formula::Ge(e),
                    -1 | 0 => Formula::Eq(e),
                    1 => Formula::Dvd(2 + rnd(2).abs(), e),
                    _ => Formula::negate(Formula::Dvd(2 + rnd(2).abs(), e)),
                };
                fs.push(f);
            }
            let eval = |f: &Formula, a: &[i128; 3]| -> bool {
                fn ev(f: &Formula, a: &[i128; 3], vars: &[Var; 3]) -> bool {
                    let val = |e: &Lin| {
                        e.konst
                            + vars
                                .iter()
                                .zip(a)
                                .map(|(w, x)| e.coef(*w) * x)
                                .sum::<i128>()
                    };
                    match f {
                        Formula::True => true,
                        Formula::False => false,
                        Formula::Ge(e) => val(e) >= 0,
                        Formula::Eq(e) => val(e) == 0,
                        Formula::Dvd(c, e) => val(e) % c == 0,
                        Formula::And(g) => g.iter().all(|h| ev(h, a, vars)),
                        Formula::Or(g) => g.iter().any(|h| ev(h, a, vars)),
                        Formula::Not(g) => !ev(g, a, vars),
                    }
                }
                ev(f, a, &vars)
            };
            let mut sat = false;
            'o: for a in -6..=6 {
                for b in -6..=6 {
                    for c in -6..=6 {
                        if fs.iter().all(|f| eval(f, &[a, b, c])) {
                            sat = true;
                            break 'o;
                        }
                    }
                }
            }
            let r = prove(&fs, &Formula::False);
            let expect = if sat {
                Verdict::Refuted
            } else {
                Verdict::Proved
            };
            assert_eq!(
                r,
                expect,
                "{:?}",
                fs.iter()
                    .map(|f| f.display(&n).to_string())
                    .collect::<Vec<_>>()
            );
        }
    }
}
