//! Linear index expressions `c0 + c1·x1 + …` over integer variables (the note's
//! "添字式"). Coefficients are `i128`; every operation is checked and returns `None` on
//! overflow, so a caller can never silently compute with a wrong number.

use std::collections::BTreeMap;
use std::fmt;

/// An index variable. Names live in a [`Names`] table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(pub u32);

/// `konst + Σ coef·var`, with no zero coefficients (so equal expressions are equal values
/// of this type).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Lin {
    pub terms: BTreeMap<Var, i128>,
    pub konst: i128,
}

/// 2^64 as an `i128`.
pub const TWO64: i128 = 1i128 << 64;

impl Lin {
    pub fn konst(c: i128) -> Lin {
        Lin {
            terms: BTreeMap::new(),
            konst: c,
        }
    }
    pub fn var(v: Var) -> Lin {
        let mut terms = BTreeMap::new();
        terms.insert(v, 1);
        Lin { terms, konst: 0 }
    }
    pub fn is_const(&self) -> bool {
        self.terms.is_empty()
    }
    pub fn as_const(&self) -> Option<i128> {
        self.is_const().then_some(self.konst)
    }
    pub fn coef(&self, v: Var) -> i128 {
        self.terms.get(&v).copied().unwrap_or(0)
    }
    /// The variable if the expression is exactly `1·x`.
    pub fn as_var(&self) -> Option<Var> {
        if self.konst != 0 || self.terms.len() != 1 {
            return None;
        }
        let (v, c) = self.terms.iter().next()?;
        (*c == 1).then_some(*v)
    }
    pub fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        self.terms.keys().copied()
    }
    pub fn add(&self, o: &Lin) -> Option<Lin> {
        let mut r = self.clone();
        r.konst = r.konst.checked_add(o.konst)?;
        for (v, c) in &o.terms {
            r.add_term(*v, *c)?;
        }
        Some(r)
    }
    pub fn sub(&self, o: &Lin) -> Option<Lin> {
        self.add(&o.scale(-1)?)
    }
    pub fn add_const(&self, c: i128) -> Option<Lin> {
        let mut r = self.clone();
        r.konst = r.konst.checked_add(c)?;
        Some(r)
    }
    pub fn scale(&self, k: i128) -> Option<Lin> {
        if k == 0 {
            return Some(Lin::default());
        }
        let mut terms = BTreeMap::new();
        for (v, c) in &self.terms {
            terms.insert(*v, c.checked_mul(k)?);
        }
        Some(Lin {
            terms,
            konst: self.konst.checked_mul(k)?,
        })
    }
    /// Adds `c·v`.
    pub fn add_term(&mut self, v: Var, c: i128) -> Option<()> {
        let n = self.coef(v).checked_add(c)?;
        if n == 0 {
            self.terms.remove(&v);
        } else {
            self.terms.insert(v, n);
        }
        Some(())
    }
    /// Replaces `v` by `e`.
    pub fn subst(&self, v: Var, e: &Lin) -> Option<Lin> {
        let c = self.coef(v);
        if c == 0 {
            return Some(self.clone());
        }
        let mut r = self.clone();
        r.terms.remove(&v);
        r.add(&e.scale(c)?)
    }
    /// Applies a substitution to every variable it maps.
    pub fn subst_all(&self, m: &BTreeMap<Var, Lin>) -> Option<Lin> {
        let mut r = Lin::konst(self.konst);
        for (v, c) in &self.terms {
            match m.get(v) {
                Some(e) => r = r.add(&e.scale(*c)?)?,
                None => r.add_term(*v, *c)?,
            }
        }
        Some(r)
    }
    /// gcd of the coefficients (0 for a constant).
    pub fn coef_gcd(&self) -> i128 {
        self.terms.values().fold(0, |g, c| gcd(g, *c))
    }
    pub fn display<'a>(&'a self, names: &'a Names) -> LinDisplay<'a> {
        LinDisplay { e: self, names }
    }
}

pub fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a as i128
}

pub fn floor_div(a: i128, b: i128) -> i128 {
    let q = a / b;
    if (a % b != 0) && ((a < 0) != (b < 0)) {
        q - 1
    } else {
        q
    }
}

pub fn ceil_div(a: i128, b: i128) -> i128 {
    -floor_div(-a, b)
}

/// The table of variable names. Ids are indices; a name is unique (fresh names get a
/// numeric suffix).
#[derive(Clone, Debug, Default)]
pub struct Names {
    names: Vec<String>,
}

impl Names {
    pub fn fresh(&mut self, base: &str) -> Var {
        let mut name = base.to_string();
        let mut i = 1;
        while self.names.contains(&name) {
            name = format!("{base}{i}");
            i += 1;
        }
        self.names.push(name);
        Var(self.names.len() as u32 - 1)
    }
    pub fn name(&self, v: Var) -> &str {
        self.names
            .get(v.0 as usize)
            .map(|s| s.as_str())
            .unwrap_or("?")
    }
    pub fn len(&self) -> usize {
        self.names.len()
    }
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

pub struct LinDisplay<'a> {
    e: &'a Lin,
    names: &'a Names,
}

impl fmt::Display for LinDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (v, c) in &self.e.terms {
            let n = self.names.name(*v);
            let (neg, a) = (*c < 0, c.unsigned_abs());
            if first {
                if neg {
                    write!(f, "-")?;
                }
            } else {
                write!(f, " {} ", if neg { "-" } else { "+" })?;
            }
            if a == 1 {
                write!(f, "{n}")?;
            } else {
                write!(f, "{}*{n}", fmt_num(a))?;
            }
            first = false;
        }
        if first {
            write!(f, "{}", fmt_signed(self.e.konst))?;
        } else if self.e.konst != 0 {
            let a = self.e.konst.unsigned_abs();
            write!(
                f,
                " {} {}",
                if self.e.konst < 0 { "-" } else { "+" },
                fmt_num(a)
            )?;
        }
        Ok(())
    }
}

/// Powers of two from 2^32 up are printed as `2^k`, so the ledger stays readable.
pub fn fmt_num(a: u128) -> String {
    if a >= 1 << 32 && a.is_power_of_two() {
        format!("2^{}", a.trailing_zeros())
    } else {
        a.to_string()
    }
}

pub fn fmt_signed(c: i128) -> String {
    if c < 0 {
        format!("-{}", fmt_num(c.unsigned_abs()))
    } else {
        fmt_num(c as u128)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn floor_and_ceil() {
        assert_eq!(floor_div(-7, 2), -4);
        assert_eq!(floor_div(7, 2), 3);
        assert_eq!(floor_div(7, -2), -4);
        assert_eq!(ceil_div(-7, 2), -3);
        assert_eq!(ceil_div(7, 2), 4);
    }

    #[test]
    fn subst_and_cancel() {
        let mut n = Names::default();
        let x = n.fresh("x");
        let y = n.fresh("y");
        let e = Lin::var(x)
            .add(&Lin::var(y).scale(3).unwrap())
            .unwrap()
            .add_const(2)
            .unwrap();
        let s = e.subst(y, &Lin::var(x).scale(-1).unwrap()).unwrap();
        assert_eq!(s.coef(x), -2);
        assert_eq!(s.coef(y), 0);
        assert_eq!(format!("{}", s.display(&n)), "-2*x + 2");
        let z = e.sub(&e).unwrap();
        assert_eq!(z, Lin::default());
    }
}
