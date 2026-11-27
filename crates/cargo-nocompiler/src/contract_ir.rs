//! The compiler adapter and RV64 lowering communicate in argument-relative terms.
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Input {
    Value(usize),
    Length(usize),
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct Expr {
    pub constant: i128,
    pub terms: BTreeMap<Input, i128>,
}
impl Expr {
    pub fn constant(value: i128) -> Self {
        Self {
            constant: value,
            terms: BTreeMap::new(),
        }
    }
    pub fn input(input: Input) -> Self {
        Self {
            constant: 0,
            terms: BTreeMap::from([(input, 1)]),
        }
    }
    pub fn add(&self, rhs: &Self, scale: i128) -> Option<Self> {
        let mut result = self.clone();
        result.constant = result
            .constant
            .checked_add(rhs.constant.checked_mul(scale)?)?;
        for (input, coefficient) in &rhs.terms {
            let value = result.terms.entry(*input).or_default();
            *value = value.checked_add(coefficient.checked_mul(scale)?)?;
        }
        result.terms.retain(|_, value| *value != 0);
        Some(result)
    }
    pub fn scale(&self, scale: i128) -> Option<Self> {
        Self::default().add(self, scale)
    }
    pub fn render(&self, name: impl Fn(Input) -> String) -> String {
        let mut result = String::new();
        for (input, coefficient) in &self.terms {
            let sign = match (result.is_empty(), *coefficient < 0) {
                (true, false) => "",
                (true, true) => "-",
                (false, false) => " + ",
                (false, true) => " - ",
            };
            result.push_str(sign);
            if coefficient.unsigned_abs() != 1 {
                result.push_str(&format!("{}*", coefficient.unsigned_abs()));
            }
            result.push_str(&name(*input));
        }
        if result.is_empty() {
            return self.constant.to_string();
        }
        if self.constant != 0 {
            let sign = if self.constant < 0 { " - " } else { " + " };
            result.push_str(&format!("{sign}{}", self.constant.unsigned_abs()));
        }
        result
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pointer {
    pub argument: usize,
    pub offset: Expr,
    pub length: Option<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Access {
    pub argument: usize,
    pub offset: Expr,
    pub bytes: Expr,
    pub alignment: u64,
    pub write: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewEnd {
    pub argument: usize,
    pub stride: u64,
    pub end: Expr,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    pub accesses: BTreeSet<Access>,
    pub returned_view: Option<Pointer>,
    pub view_end: Option<ViewEnd>,
    pub widened_view_joins: usize,
    pub returned_scalar: Option<Expr>,
    pub field_writes: BTreeMap<(usize, u64), Expr>,
    pub drops: BTreeSet<usize>,
    pub unresolved_access: bool,
}

impl Expr {
    fn encode(&self) -> String {
        let mut parts = vec![self.constant.to_string()];
        for (input, coefficient) in &self.terms {
            let tag = match input {
                Input::Value(index) => format!("v{index}"),
                Input::Length(index) => format!("l{index}"),
            };
            parts.push(format!("{tag}={coefficient}"));
        }
        parts.join(",")
    }
    fn decode(text: &str) -> Option<Self> {
        let mut parts = text.split(',');
        let mut value = Self::constant(parts.next()?.parse().ok()?);
        for part in parts {
            let (input, coefficient) = part.split_once('=')?;
            let index = input.get(1..)?.parse().ok()?;
            let key = match input.as_bytes().first()? {
                b'v' => Input::Value(index),
                b'l' => Input::Length(index),
                _ => return None,
            };
            value.terms.insert(key, coefficient.parse().ok()?);
        }
        Some(value)
    }
}

impl Summary {
    pub fn encode(&self, symbol: &str, out: &mut String) {
        use std::fmt::Write as _;
        let _ = writeln!(out, "{symbol}\tanalyzed");
        for access in &self.accesses {
            let _ = writeln!(
                out,
                "{symbol}\taccess\t{}\t{}\t{}\t{}\t{}",
                access.argument,
                access.offset.encode(),
                access.bytes.encode(),
                access.alignment,
                access.write
            );
        }
        if let Some(pointer) = &self.returned_view
            && let Some(length) = &pointer.length
        {
            let _ = writeln!(
                out,
                "{symbol}\tview\t{}\t{}\t{}",
                pointer.argument,
                pointer.offset.encode(),
                length.encode()
            );
        }
        if self.widened_view_joins != 0 {
            let _ = writeln!(
                out,
                "{symbol}\twidened_view_joins\t{}",
                self.widened_view_joins
            );
        }
        if let Some(view) = &self.view_end {
            let _ = writeln!(
                out,
                "{symbol}\tview_end\t{}\t{}\t{}",
                view.argument,
                view.stride,
                view.end.encode()
            );
        }
        if let Some(value) = &self.returned_scalar {
            let _ = writeln!(out, "{symbol}\treturn\t{}", value.encode());
        }
        for ((argument, offset), value) in &self.field_writes {
            let _ = writeln!(
                out,
                "{symbol}\tfield\t{argument}\t{offset}\t{}",
                value.encode()
            );
        }
        for argument in &self.drops {
            let _ = writeln!(out, "{symbol}\tdrop\t{argument}");
        }
        if self.unresolved_access {
            let _ = writeln!(out, "{symbol}\tunresolved");
        }
    }

    pub fn decode(record: &str) -> Option<BTreeMap<String, Self>> {
        let mut summaries = BTreeMap::<String, Self>::new();
        for line in record.lines() {
            let mut fields = line.split('\t');
            let summary = summaries.entry(fields.next()?.into()).or_default();
            match fields.next()? {
                "analyzed" => {}
                "access" => {
                    summary.accesses.insert(Access {
                        argument: fields.next()?.parse().ok()?,
                        offset: Expr::decode(fields.next()?)?,
                        bytes: Expr::decode(fields.next()?)?,
                        alignment: fields.next()?.parse().ok()?,
                        write: fields.next()?.parse().ok()?,
                    });
                }
                "view" => {
                    summary.returned_view = Some(Pointer {
                        argument: fields.next()?.parse().ok()?,
                        offset: Expr::decode(fields.next()?)?,
                        length: Some(Expr::decode(fields.next()?)?),
                    })
                }
                "widened_view_joins" => summary.widened_view_joins = fields.next()?.parse().ok()?,
                "view_end" => {
                    summary.view_end = Some(ViewEnd {
                        argument: fields.next()?.parse().ok()?,
                        stride: fields.next()?.parse().ok()?,
                        end: Expr::decode(fields.next()?)?,
                    });
                }
                "return" => summary.returned_scalar = Some(Expr::decode(fields.next()?)?),
                "field" => {
                    summary.field_writes.insert(
                        (fields.next()?.parse().ok()?, fields.next()?.parse().ok()?),
                        Expr::decode(fields.next()?)?,
                    );
                }
                "drop" => {
                    summary.drops.insert(fields.next()?.parse().ok()?);
                }
                "unresolved" => summary.unresolved_access = true,
                _ => return None,
            }
            if fields.next().is_some() {
                return None;
            }
        }
        Some(summaries)
    }
}
