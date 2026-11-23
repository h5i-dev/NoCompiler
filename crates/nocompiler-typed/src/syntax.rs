//! The annotation language (signatures, loop invariants, join annotations, hints): a
//! lexer and a recursive-descent parser producing a syntax tree whose variables are still
//! names. The grammar is in docs/typed/syntax.md.

use crate::isa::Reg;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Num(i128),
    /// Punctuation and operators, normalised to ASCII: `|->` `<=` `>=` `!=` `<` `>` `=`
    /// `|` (divides) `&&` `||` `!` `=>` `->` `+` `-` `*` `^` `(` `)` `[` `]` `{` `}` `,`
    /// `:` `:=`.
    P(&'static str),
}

pub fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let cs: Vec<char> = s.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c.is_ascii_digit() {
            let st = i;
            if c == '0' && i + 1 < cs.len() && (cs[i + 1] == 'x' || cs[i + 1] == 'X') {
                i += 2;
                while i < cs.len() && (cs[i].is_ascii_hexdigit() || cs[i] == '_') {
                    i += 1;
                }
                let t: String = cs[st + 2..i].iter().filter(|c| **c != '_').collect();
                let v = i128::from_str_radix(&t, 16).map_err(|e| format!("bad number: {e}"))?;
                out.push(Tok::Num(v));
            } else {
                while i < cs.len() && (cs[i].is_ascii_digit() || cs[i] == '_') {
                    i += 1;
                }
                let t: String = cs[st..i].iter().filter(|c| **c != '_').collect();
                out.push(Tok::Num(
                    t.parse().map_err(|e| format!("bad number {t}: {e}"))?,
                ));
            }
            continue;
        }
        if c.is_alphabetic() || c == '_' || c == '.' || c == '@' {
            // `@sym`: the address of the data symbol sym (I32)
            let st = i;
            if c == '@' {
                i += 1;
            }
            while i < cs.len()
                && (cs[i].is_alphanumeric() || cs[i] == '_' || cs[i] == '\'' || cs[i] == '.')
            {
                i += 1;
            }
            out.push(Tok::Ident(cs[st..i].iter().collect()));
            continue;
        }
        let rest: String = cs[i..cs.len().min(i + 3)].iter().collect();
        let (p, n): (&'static str, usize) = if rest.starts_with("|->") {
            ("|->", 3)
        } else if rest.starts_with("<=") {
            ("<=", 2)
        } else if rest.starts_with(">=") {
            (">=", 2)
        } else if rest.starts_with("!=") {
            ("!=", 2)
        } else if rest.starts_with("&&") {
            ("&&", 2)
        } else if rest.starts_with("||") {
            ("||", 2)
        } else if rest.starts_with("=>") {
            ("=>", 2)
        } else if rest.starts_with("->") {
            ("->", 2)
        } else if rest.starts_with(":=") {
            (":=", 2)
        } else {
            let p = match c {
                '↦' => "|->",
                '≤' => "<=",
                '≥' => ">=",
                '≠' => "!=",
                '<' => "<",
                '>' => ">",
                '=' => "=",
                '|' | '∣' => "|",
                '∧' => "&&",
                '∨' => "||",
                '¬' | '!' => "!",
                '⇒' => "=>",
                '→' => "->",
                '+' => "+",
                '-' | '−' => "-",
                '*' | '·' | '×' => "*",
                '^' => "^",
                '(' => "(",
                ')' => ")",
                '[' => "[",
                ']' => "]",
                '{' => "{",
                '}' => "}",
                ',' => ",",
                ':' => ":",
                _ => return Err(format!("unexpected character '{c}'")),
            };
            (p, 1)
        };
        out.push(Tok::P(p));
        i += n;
    }
    Ok(out)
}

/// A linear expression over names.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SLin {
    pub terms: BTreeMap<String, i128>,
    pub konst: i128,
}

impl SLin {
    fn konst(c: i128) -> SLin {
        SLin {
            terms: BTreeMap::new(),
            konst: c,
        }
    }
    fn var(n: &str) -> SLin {
        let mut terms = BTreeMap::new();
        terms.insert(n.to_string(), 1);
        SLin { terms, konst: 0 }
    }
    fn add(&self, o: &SLin, sign: i128) -> Option<SLin> {
        let mut r = self.clone();
        r.konst = r.konst.checked_add(o.konst.checked_mul(sign)?)?;
        for (v, c) in &o.terms {
            let n = r
                .terms
                .get(v)
                .copied()
                .unwrap_or(0)
                .checked_add(c.checked_mul(sign)?)?;
            if n == 0 {
                r.terms.remove(v);
            } else {
                r.terms.insert(v.clone(), n);
            }
        }
        Some(r)
    }
    fn scale(&self, k: i128) -> Option<SLin> {
        if k == 0 {
            return Some(SLin::default());
        }
        let mut r = SLin::konst(self.konst.checked_mul(k)?);
        for (v, c) in &self.terms {
            r.terms.insert(v.clone(), c.checked_mul(k)?);
        }
        Some(r)
    }
    pub fn as_const(&self) -> Option<i128> {
        self.terms.is_empty().then_some(self.konst)
    }
    /// The name if the expression is a bare variable.
    pub fn as_var(&self) -> Option<&str> {
        if self.konst != 0 || self.terms.len() != 1 {
            return None;
        }
        let (n, c) = self.terms.iter().next()?;
        (*c == 1).then_some(n.as_str())
    }
    pub fn names(&self) -> impl Iterator<Item = &String> {
        self.terms.keys()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum SFormula {
    True,
    False,
    Le(SLin, SLin),
    Lt(SLin, SLin),
    Eq(SLin, SLin),
    Ne(SLin, SLin),
    Dvd(i128, SLin),
    And(Vec<SFormula>),
    Or(Vec<SFormula>),
    Not(Box<SFormula>),
    Implies(Box<SFormula>, Box<SFormula>),
}

impl SFormula {
    pub fn names(&self, out: &mut Vec<String>) {
        match self {
            SFormula::True | SFormula::False => {}
            SFormula::Le(a, b) | SFormula::Lt(a, b) | SFormula::Eq(a, b) | SFormula::Ne(a, b) => {
                out.extend(a.names().cloned());
                out.extend(b.names().cloned());
            }
            SFormula::Dvd(_, e) => out.extend(e.names().cloned()),
            SFormula::And(v) | SFormula::Or(v) => v.iter().for_each(|f| f.names(out)),
            SFormula::Not(f) => f.names(out),
            SFormula::Implies(a, b) => {
                a.names(out);
                b.names(out);
            }
        }
    }
}

/// A register's type: `int(e)`, `int` (`None`), `u64(e)`, `i64(e)`.
#[derive(Clone, Debug, PartialEq)]
pub struct SRegTy {
    pub reg: Reg,
    pub expr: Option<SLin>,
    /// The range `u64`/`i64` adds.
    pub range: Option<RangeKind>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeKind {
    U64,
    I64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Ro,
    Rw,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SField {
    pub off: i128,
    pub ty: SLin,
}

#[derive(Clone, Debug, PartialEq)]
pub enum SCapKind {
    Bytes {
        base: SLin,
        len: SLin,
        mode: Mode,
        heap: bool,
        fields: Vec<SField>,
        /// `-> {…}`: the fields on exit (I6); `None` means the entry fields.
        out_fields: Option<Vec<SField>>,
    },
    Token(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct SCap {
    pub guard: Option<SFormula>,
    pub kind: SCapKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FnKind {
    Safe,
    Unsafe,
    Extern,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct SFrame {
    pub size: i128,
    pub slots: Vec<i128>,
    pub addr: Vec<(i128, i128)>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct SSig {
    pub name: String,
    pub kind: FnKind,
    pub partial: bool,
    pub params: Vec<String>,
    pub ins: Vec<SRegTy>,
    pub borrow: Vec<SCap>,
    pub take: Vec<SCap>,
    pub pre: Vec<SFormula>,
    pub outs: Vec<SRegTy>,
    pub give: Vec<SCap>,
    pub post: Vec<SFormula>,
    pub stack: Option<i128>,
    pub frame: Option<SFrame>,
}

/// `inv` (a loop head) or `join` (a forward join point).
#[derive(Clone, Debug, PartialEq)]
pub struct SInv {
    pub is_loop: bool,
    pub vars: Vec<String>,
    pub regs: Vec<SRegTy>,
    pub wher: Vec<SFormula>,
    pub decreases: Option<SLin>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Annot {
    Sig(SSig),
    Inv(SInv),
    /// `with x := e, …`: instantiation hints for the next instruction.
    With(Vec<(String, SLin)>),
}

const KEYWORDS: &[&str] = &[
    "in",
    "out",
    "borrow",
    "take",
    "give",
    "where",
    "stack",
    "frame",
    "partial",
    "decreases",
    "fn",
    "unsafe",
    "extern",
    "inv",
    "join",
    "with",
];

struct P<'a> {
    t: &'a [Tok],
    i: usize,
}

type R<T> = Result<T, String>;

impl<'a> P<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.t.get(self.i)
    }
    fn peek_p(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::P(q)) if *q == p)
    }
    fn peek_kw(&self, k: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(q)) if q == k)
    }
    fn at_keyword(&self) -> bool {
        matches!(self.peek(), Some(Tok::Ident(q)) if KEYWORDS.contains(&q.as_str()))
    }
    fn eat_p(&mut self, p: &str) -> bool {
        if self.peek_p(p) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn eat_kw(&mut self, k: &str) -> bool {
        if self.peek_kw(k) {
            self.i += 1;
            true
        } else {
            false
        }
    }
    fn expect_p(&mut self, p: &str) -> R<()> {
        if self.eat_p(p) {
            Ok(())
        } else {
            Err(format!("expected '{p}', found {}", self.here()))
        }
    }
    fn here(&self) -> String {
        match self.peek() {
            None => "end of annotation".into(),
            Some(Tok::Ident(s)) => format!("'{s}'"),
            Some(Tok::Num(n)) => format!("'{n}'"),
            Some(Tok::P(p)) => format!("'{p}'"),
        }
    }
    fn ident(&mut self) -> R<String> {
        match self.peek() {
            Some(Tok::Ident(s)) if !KEYWORDS.contains(&s.as_str()) => {
                let s = s.clone();
                self.i += 1;
                Ok(s)
            }
            _ => Err(format!("expected a name, found {}", self.here())),
        }
    }
    fn num(&mut self) -> R<i128> {
        let neg = self.eat_p("-");
        let v = match self.peek() {
            Some(Tok::Num(n)) => {
                let n = *n;
                self.i += 1;
                n
            }
            _ => return Err(format!("expected a number, found {}", self.here())),
        };
        let v = if self.eat_p("^") {
            pow(v, self.num()?)?
        } else {
            v
        };
        Ok(if neg { -v } else { v })
    }

    // expr := term (('+'|'-') term)*
    fn expr(&mut self) -> R<SLin> {
        let mut e = if self.eat_p("-") {
            self.term()?.scale(-1).ok_or_else(ovf)?
        } else {
            self.term()?
        };
        loop {
            if self.eat_p("+") {
                e = e.add(&self.term()?, 1).ok_or_else(ovf)?;
            } else if self.eat_p("-") {
                e = e.add(&self.term()?, -1).ok_or_else(ovf)?;
            } else {
                return Ok(e);
            }
        }
    }
    // term := factor (('*') factor)* | NUM factor (juxtaposition)
    fn term(&mut self) -> R<SLin> {
        let mut e = self.factor()?;
        loop {
            let juxt = e.as_const().is_some()
                && matches!(self.peek(), Some(Tok::Ident(s)) if !KEYWORDS.contains(&s.as_str()))
                || e.as_const().is_some() && self.peek_p("(");
            if self.eat_p("*") || juxt {
                let f = self.factor()?;
                e = match (e.as_const(), f.as_const()) {
                    (Some(c), _) => f.scale(c).ok_or_else(ovf)?,
                    (_, Some(c)) => e.scale(c).ok_or_else(ovf)?,
                    _ => return Err("non-linear product of two variables".into()),
                };
            } else {
                return Ok(e);
            }
        }
    }
    fn factor(&mut self) -> R<SLin> {
        match self.peek().cloned() {
            Some(Tok::Num(_)) => Ok(SLin::konst(self.num()?)),
            Some(Tok::Ident(s)) if !KEYWORDS.contains(&s.as_str()) => {
                self.i += 1;
                Ok(SLin::var(&s))
            }
            Some(Tok::P("(")) => {
                self.i += 1;
                let e = self.expr()?;
                self.expect_p(")")?;
                Ok(e)
            }
            Some(Tok::P("-")) => {
                self.i += 1;
                self.factor()?.scale(-1).ok_or_else(ovf)
            }
            _ => Err(format!("expected an expression, found {}", self.here())),
        }
    }

    // formula := imp ; imp := or ('=>' imp)? ; or := and ('||' and)* ; and := un ('&&' un)*
    fn formula(&mut self) -> R<SFormula> {
        let a = self.or()?;
        if self.eat_p("=>") {
            let b = self.formula()?;
            return Ok(SFormula::Implies(Box::new(a), Box::new(b)));
        }
        Ok(a)
    }
    fn or(&mut self) -> R<SFormula> {
        let mut v = vec![self.and()?];
        while self.eat_p("||") {
            v.push(self.and()?);
        }
        Ok(if v.len() == 1 {
            v.pop().unwrap()
        } else {
            SFormula::Or(v)
        })
    }
    fn and(&mut self) -> R<SFormula> {
        let mut v = vec![self.unary()?];
        while self.eat_p("&&") {
            v.push(self.unary()?);
        }
        Ok(if v.len() == 1 {
            v.pop().unwrap()
        } else {
            SFormula::And(v)
        })
    }
    fn unary(&mut self) -> R<SFormula> {
        if self.eat_p("!") {
            return Ok(SFormula::Not(Box::new(self.unary()?)));
        }
        if self.eat_kw("true") {
            return Ok(SFormula::True);
        }
        if self.eat_kw("false") {
            return Ok(SFormula::False);
        }
        // `( formula )` or a comparison starting with a parenthesised expression.
        if self.peek_p("(") {
            let save = self.i;
            if let Ok(f) = self.comparison() {
                return Ok(f);
            }
            self.i = save;
            self.i += 1;
            let f = self.formula()?;
            self.expect_p(")")?;
            return Ok(f);
        }
        self.comparison()
    }
    /// `e1 op e2 op e3 …` (chained), or `c | e`.
    fn comparison(&mut self) -> R<SFormula> {
        let first = self.expr()?;
        if self.eat_p("|") {
            let c = first
                .as_const()
                .ok_or("the left of '|' (divides) must be a constant")?;
            if c <= 0 {
                return Err("the divisor must be positive".into());
            }
            return Ok(SFormula::Dvd(c, self.expr()?));
        }
        let mut parts = Vec::new();
        let mut lhs = first;
        loop {
            let op = match self.peek() {
                Some(Tok::P(p)) if ["<=", "<", ">=", ">", "=", "!="].contains(p) => *p,
                _ => break,
            };
            self.i += 1;
            let rhs = self.expr()?;
            parts.push(match op {
                "<=" => SFormula::Le(lhs.clone(), rhs.clone()),
                "<" => SFormula::Lt(lhs.clone(), rhs.clone()),
                ">=" => SFormula::Le(rhs.clone(), lhs.clone()),
                ">" => SFormula::Lt(rhs.clone(), lhs.clone()),
                "=" => SFormula::Eq(lhs.clone(), rhs.clone()),
                _ => SFormula::Ne(lhs.clone(), rhs.clone()),
            });
            lhs = rhs;
        }
        match parts.len() {
            0 => Err(format!("expected a comparison, found {}", self.here())),
            1 => Ok(parts.pop().unwrap()),
            _ => Ok(SFormula::And(parts)),
        }
    }

    fn regty(&mut self) -> R<SRegTy> {
        let name = match self.peek() {
            Some(Tok::Ident(s)) => s.clone(),
            _ => return Err(format!("expected a register, found {}", self.here())),
        };
        let reg = Reg::parse(&name).ok_or_else(|| format!("'{name}' is not a register"))?;
        self.i += 1;
        self.expect_p(":")?;
        let ty = self.ident()?;
        let (expr, range) = match ty.as_str() {
            "int" => {
                if self.eat_p("(") {
                    let e = self.expr()?;
                    self.expect_p(")")?;
                    (Some(e), None)
                } else {
                    (None, None)
                }
            }
            "u64" | "i64" => {
                self.expect_p("(")?;
                let e = self.expr()?;
                self.expect_p(")")?;
                (
                    Some(e),
                    Some(if ty == "u64" {
                        RangeKind::U64
                    } else {
                        RangeKind::I64
                    }),
                )
            }
            _ => return Err(format!("unknown type '{ty}' (int, u64, i64)")),
        };
        Ok(SRegTy { reg, expr, range })
    }

    fn fields(&mut self) -> R<Vec<SField>> {
        self.expect_p("{")?;
        let mut v = Vec::new();
        if !self.eat_p("}") {
            loop {
                let off = self.num()?;
                self.expect_p(":")?;
                if !self.eat_kw("int") {
                    return Err(format!(
                        "expected 'int(e)' for a field, found {}",
                        self.here()
                    ));
                }
                self.expect_p("(")?;
                let ty = self.expr()?;
                self.expect_p(")")?;
                v.push(SField { off, ty });
                if self.eat_p("}") {
                    break;
                }
                self.expect_p(",")?;
            }
        }
        Ok(v)
    }

    fn cap(&mut self, guarded: bool) -> R<SCap> {
        // A guard is a formula followed by `=>`; try it first.
        let mut guard = None;
        if guarded {
            let save = self.i;
            match self.or() {
                Ok(g) if self.eat_p("=>") => guard = Some(g),
                _ => self.i = save,
            }
        }
        // A token: a capitalised name that is not followed by `|->`.
        if let Some(Tok::Ident(s)) = self.peek().cloned()
            && !KEYWORDS.contains(&s.as_str())
            && matches!(
                self.t.get(self.i + 1),
                None | Some(Tok::P(",")) | Some(Tok::Ident(_))
            )
            && s.chars().next().is_some_and(|c| c.is_uppercase())
        {
            self.i += 1;
            return Ok(SCap {
                guard,
                kind: SCapKind::Token(s),
            });
        }
        let base = self.expr()?;
        self.expect_p("|->")?;
        if !self.eat_kw("bytes") {
            return Err(format!("expected 'bytes', found {}", self.here()));
        }
        self.expect_p("[")?;
        let len = self.expr()?;
        self.expect_p("]")?;
        let mode = if self.eat_kw("rw") {
            Mode::Rw
        } else if self.eat_kw("ro") {
            Mode::Ro
        } else {
            return Err(format!("expected 'ro' or 'rw', found {}", self.here()));
        };
        let heap = self.eat_kw("heap");
        let fields = if self.peek_p("{") {
            self.fields()?
        } else {
            Vec::new()
        };
        let out_fields = if self.eat_p("->") {
            Some(self.fields()?)
        } else {
            None
        };
        Ok(SCap {
            guard,
            kind: SCapKind::Bytes {
                base,
                len,
                mode,
                heap,
                fields,
                out_fields,
            },
        })
    }

    fn list<T>(&mut self, mut f: impl FnMut(&mut Self) -> R<T>) -> R<Vec<T>> {
        let mut v = vec![f(self)?];
        while self.eat_p(",") {
            v.push(f(self)?);
        }
        Ok(v)
    }

    fn names_in_brackets(&mut self) -> R<Vec<String>> {
        let mut v = Vec::new();
        if self.eat_p("[") && !self.eat_p("]") {
            v = self.list(|p| p.ident())?;
            self.expect_p("]")?;
        }
        Ok(v)
    }

    fn sig(&mut self) -> R<SSig> {
        let mut kind = FnKind::Safe;
        let mut partial = false;
        loop {
            if self.eat_kw("unsafe") {
                kind = FnKind::Unsafe;
            } else if self.eat_kw("extern") {
                kind = FnKind::Extern;
            } else if self.eat_kw("partial") {
                partial = true;
            } else {
                break;
            }
        }
        if !self.eat_kw("fn") {
            return Err(format!("expected 'fn', found {}", self.here()));
        }
        let name = match self.peek() {
            Some(Tok::Ident(s)) => s.clone(),
            _ => return Err("expected the function name".into()),
        };
        self.i += 1;
        let params = self.names_in_brackets()?;
        let mut s = SSig {
            name,
            kind,
            partial,
            params,
            ins: vec![],
            borrow: vec![],
            take: vec![],
            pre: vec![],
            outs: vec![],
            give: vec![],
            post: vec![],
            stack: None,
            frame: None,
        };
        let mut exit_side = false;
        while self.peek().is_some() {
            if self.eat_kw("in") {
                s.ins.extend(self.list(|p| p.regty())?);
            } else if self.eat_kw("out") {
                exit_side = true;
                s.outs.extend(self.list(|p| p.regty())?);
            } else if self.eat_kw("borrow") {
                s.borrow.extend(self.list(|p| p.cap(false))?);
            } else if self.eat_kw("take") {
                s.take.extend(self.list(|p| p.cap(false))?);
            } else if self.eat_kw("give") {
                exit_side = true;
                s.give.extend(self.list(|p| p.cap(true))?);
            } else if self.eat_kw("where") {
                let fs = self.list(|p| p.formula())?;
                if exit_side {
                    s.post.extend(fs)
                } else {
                    s.pre.extend(fs)
                }
            } else if self.eat_kw("stack") {
                s.stack = Some(self.num()?);
            } else if self.eat_kw("partial") {
                s.partial = true;
            } else if self.eat_kw("frame") {
                let mut fr = SFrame {
                    size: self.num()?,
                    ..Default::default()
                };
                loop {
                    if self.eat_kw("slots") {
                        fr.slots = self.list(|p| p.num())?;
                    } else if self.eat_kw("addr") {
                        fr.addr = self.list(|p| {
                            p.expect_p("[")?;
                            let a = p.num()?;
                            p.expect_p(",")?;
                            let b = p.num()?;
                            p.expect_p(")")?;
                            Ok((a, b - a))
                        })?;
                    } else {
                        break;
                    }
                }
                s.frame = Some(fr);
            } else {
                return Err(format!(
                    "expected a clause (in, out, borrow, take, give, where, stack, frame), found {}",
                    self.here()
                ));
            }
        }
        Ok(s)
    }

    fn inv(&mut self, is_loop: bool) -> R<SInv> {
        let vars = self.names_in_brackets()?;
        let mut inv = SInv {
            is_loop,
            vars,
            regs: vec![],
            wher: vec![],
            decreases: None,
        };
        if matches!(self.peek(), Some(Tok::Ident(s)) if Reg::parse(s).is_some()) {
            inv.regs = self.list(|p| p.regty())?;
        }
        while self.peek().is_some() {
            if self.eat_kw("where") {
                inv.wher.extend(self.list(|p| p.formula())?);
            } else if is_loop && self.eat_kw("decreases") {
                inv.decreases = Some(self.expr()?);
            } else {
                return Err(format!(
                    "expected 'where' or 'decreases', found {}",
                    self.here()
                ));
            }
        }
        Ok(inv)
    }
}

fn ovf() -> String {
    "integer overflow in an annotation".into()
}

fn pow(b: i128, e: i128) -> R<i128> {
    if !(0..=126).contains(&e) {
        return Err(format!("exponent {e} out of range"));
    }
    b.checked_pow(e as u32).ok_or_else(ovf)
}

/// Parses one annotation (the text of a `#:` block, joined).
pub fn parse_annot(text: &str) -> R<Annot> {
    let toks = lex(text)?;
    let mut p = P { t: &toks, i: 0 };
    let a = if p.peek_kw("inv") {
        p.i += 1;
        Annot::Inv(p.inv(true)?)
    } else if p.peek_kw("join") {
        p.i += 1;
        Annot::Inv(p.inv(false)?)
    } else if p.peek_kw("with") {
        p.i += 1;
        Annot::With(p.list(|p| {
            let n = p.ident()?;
            p.expect_p(":=")?;
            Ok((n, p.expr()?))
        })?)
    } else {
        Annot::Sig(p.sig()?)
    };
    if p.peek().is_some() {
        return Err(format!("unexpected {} at the end", p.here()));
    }
    let _ = p.at_keyword();
    Ok(a)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sum_signature() {
        let a = parse_annot(
            "fn sum [ρ, n] in a0: int(ρ), a1: int(n) borrow ρ ↦ bytes[8n] ro where 8 ∣ ρ out a0: int stack 0",
        )
        .unwrap();
        let Annot::Sig(s) = a else { panic!() };
        assert_eq!(s.params, vec!["ρ", "n"]);
        assert_eq!(s.ins.len(), 2);
        assert_eq!(s.outs[0].expr, None);
        let SCapKind::Bytes { len, mode, .. } = &s.borrow[0].kind else {
            panic!()
        };
        assert_eq!(len.terms.get("n"), Some(&8));
        assert_eq!(*mode, Mode::Ro);
        assert_eq!(s.pre, vec![SFormula::Dvd(8, SLin::var("ρ"))]);
        assert_eq!(s.stack, Some(0));
    }

    #[test]
    fn malloc_contract() {
        let a = parse_annot(
            "unsafe fn malloc [n] in a0: int(n) borrow Heap where 0 ≤ n < 2^64 \
             out a0: int(p) give p ≠ 0 ⇒ p ↦ bytes[n] rw heap where 0 ≤ p < 2^64, 16 ∣ p",
        )
        .unwrap();
        let Annot::Sig(s) = a else { panic!() };
        assert_eq!(s.kind, FnKind::Unsafe);
        assert!(matches!(s.borrow[0].kind, SCapKind::Token(ref t) if t == "Heap"));
        assert_eq!(s.pre.len(), 1);
        assert_eq!(s.post.len(), 2);
        assert!(s.give[0].guard.is_some());
        let SCapKind::Bytes { heap, .. } = &s.give[0].kind else {
            panic!()
        };
        assert!(heap);
    }

    #[test]
    fn inv_and_fields() {
        let a = parse_annot(
            "inv [m] a0: int(ρ + 8n − 8m), a1: int(m), a2: int where 1 ≤ m ≤ n decreases m",
        )
        .unwrap();
        let Annot::Inv(i) = a else { panic!() };
        assert_eq!(i.regs.len(), 3);
        assert!(matches!(&i.wher[0], SFormula::And(v) if v.len() == 2));
        assert!(i.decreases.is_some());
        let a = parse_annot(
            "fn parse [ρ, β, n] in a0: int(ρ) borrow ρ |-> bytes[16] ro {0: int(β), 8: int(n)}, β |-> bytes[n] ro where 8 | ρ out a0: int",
        )
        .unwrap();
        let Annot::Sig(s) = a else { panic!() };
        assert_eq!(s.borrow.len(), 2);
        let SCapKind::Bytes { fields, .. } = &s.borrow[0].kind else {
            panic!()
        };
        assert_eq!(fields.len(), 2);
        let a = parse_annot("fn f [] frame 80 slots 72 addr [0, 64) out a0: int stack 80").unwrap();
        let Annot::Sig(s) = a else { panic!() };
        assert_eq!(
            s.frame,
            Some(SFrame {
                size: 80,
                slots: vec![72],
                addr: vec![(0, 64)]
            })
        );
    }

    #[test]
    fn formulas() {
        let a = parse_annot("join where (x < 3 || x = 5) && !(2 | x), 8(n - 1) + 2 ≥ 0").unwrap();
        let Annot::Inv(i) = a else { panic!() };
        assert_eq!(i.wher.len(), 2);
        assert!(parse_annot("join where x * y = 0").is_err());
        assert!(parse_annot("with n := 8k + 1").is_ok());
    }
}
