//! Quantifier-free Presburger formulas (the note's "制約" ψ).

use crate::lin::{Lin, Names, Var, fmt_num};
use std::collections::BTreeSet;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    True,
    False,
    /// `e ≥ 0`.
    Ge(Lin),
    /// `e = 0`.
    Eq(Lin),
    /// The positive constant divides `e`.
    Dvd(i128, Lin),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Not(Box<Formula>),
}

impl Formula {
    /// `a ≤ b`. `None` on overflow.
    pub fn le(a: &Lin, b: &Lin) -> Option<Formula> {
        Some(Formula::Ge(b.sub(a)?))
    }
    /// `a < b`.
    pub fn lt(a: &Lin, b: &Lin) -> Option<Formula> {
        Some(Formula::Ge(b.sub(a)?.add_const(-1)?))
    }
    pub fn eq(a: &Lin, b: &Lin) -> Option<Formula> {
        Some(Formula::Eq(a.sub(b)?))
    }
    /// `a ≡ b (mod 2^64)`.
    pub fn eq64(a: &Lin, b: &Lin) -> Option<Formula> {
        Some(Formula::Dvd(crate::lin::TWO64, a.sub(b)?))
    }
    pub fn negate(f: Formula) -> Formula {
        match f {
            Formula::True => Formula::False,
            Formula::False => Formula::True,
            Formula::Not(g) => *g,
            g => Formula::Not(Box::new(g)),
        }
    }
    pub fn and(fs: Vec<Formula>) -> Formula {
        let fs: Vec<_> = fs.into_iter().filter(|f| *f != Formula::True).collect();
        if fs.contains(&Formula::False) {
            return Formula::False;
        }
        match fs.len() {
            0 => Formula::True,
            1 => fs.into_iter().next().unwrap(),
            _ => Formula::And(fs),
        }
    }
    pub fn or(fs: Vec<Formula>) -> Formula {
        let fs: Vec<_> = fs.into_iter().filter(|f| *f != Formula::False).collect();
        if fs.contains(&Formula::True) {
            return Formula::True;
        }
        match fs.len() {
            0 => Formula::False,
            1 => fs.into_iter().next().unwrap(),
            _ => Formula::Or(fs),
        }
    }
    /// `0 ≤ e < 2^64`.
    pub fn in_u64(e: &Lin) -> Option<Formula> {
        Some(Formula::and(vec![
            Formula::Ge(e.clone()),
            Formula::lt(e, &Lin::konst(crate::lin::TWO64))?,
        ]))
    }
    pub fn vars(&self, out: &mut BTreeSet<Var>) {
        match self {
            Formula::True | Formula::False => {}
            Formula::Ge(e) | Formula::Eq(e) | Formula::Dvd(_, e) => out.extend(e.vars()),
            Formula::And(fs) | Formula::Or(fs) => fs.iter().for_each(|f| f.vars(out)),
            Formula::Not(f) => f.vars(out),
        }
    }
    /// Applies `f` to every expression.
    pub fn map_lin(&self, f: &mut impl FnMut(&Lin) -> Option<Lin>) -> Option<Formula> {
        Some(match self {
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Ge(e) => Formula::Ge(f(e)?),
            Formula::Eq(e) => Formula::Eq(f(e)?),
            Formula::Dvd(c, e) => Formula::Dvd(*c, f(e)?),
            Formula::And(fs) => {
                Formula::And(fs.iter().map(|g| g.map_lin(f)).collect::<Option<_>>()?)
            }
            Formula::Or(fs) => Formula::Or(fs.iter().map(|g| g.map_lin(f)).collect::<Option<_>>()?),
            Formula::Not(g) => Formula::Not(Box::new(g.map_lin(f)?)),
        })
    }
    /// The conjuncts of a top-level conjunction.
    pub fn conjuncts(self) -> Vec<Formula> {
        match self {
            Formula::And(fs) => fs.into_iter().flat_map(|f| f.conjuncts()).collect(),
            Formula::True => vec![],
            f => vec![f],
        }
    }
    pub fn display<'a>(&'a self, names: &'a Names) -> FormulaDisplay<'a> {
        FormulaDisplay { f: self, names }
    }
}

pub struct FormulaDisplay<'a> {
    f: &'a Formula,
    names: &'a Names,
}

impl fmt::Display for FormulaDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let n = self.names;
        match self.f {
            Formula::True => write!(f, "true"),
            Formula::False => write!(f, "false"),
            Formula::Ge(e) => write!(f, "{} >= 0", e.display(n)),
            Formula::Eq(e) => write!(f, "{} = 0", e.display(n)),
            Formula::Dvd(c, e) => write!(f, "{} | {}", fmt_num(*c as u128), e.display(n)),
            Formula::And(fs) | Formula::Or(fs) => {
                let op = if matches!(self.f, Formula::And(_)) {
                    " && "
                } else {
                    " || "
                };
                write!(f, "(")?;
                for (i, g) in fs.iter().enumerate() {
                    if i > 0 {
                        write!(f, "{op}")?;
                    }
                    write!(f, "{}", g.display(n))?;
                }
                write!(f, ")")
            }
            Formula::Not(g) => write!(f, "!({})", g.display(n)),
        }
    }
}
