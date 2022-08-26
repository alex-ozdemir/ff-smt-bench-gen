//! SMT printing without duplication
//!
//! rsmt2 duplicates a ton.

use circ::ir::term::*;
use std::collections::HashMap;
use std::io::Write;

struct Printer<'a, W: 'a> {
    sort_reprs: HashMap<Sort, String>,
    term_reprs: TermMap<String>,
    writer: &'a mut W,
    n_ff_sorts: usize,
    n_terms: usize,
}

fn get_logic_string(t: Term) -> String {
    let mut ff = false;
    let mut bv = false;
    let mut nia = false;
    for t in PostOrderIter::new(t) {
        match check(&t) {
            Sort::Field(..) => ff = true,
            Sort::BitVector(..) => bv = true,
            Sort::Int => nia = true,
            Sort::Bool => {}
            s => unimplemented!("{}", s),
        }
    }
    format!(
        "QF_{}{}{}",
        if bv { "BV" } else { "" },
        if ff { "FF" } else { "" },
        if nia { "NIA" } else { "" },
    )
}

impl<'a, W: 'a + Write> Printer<'a, W> {
    fn new(writer: &'a mut W) -> Self {
        Self {
            sort_reprs: Default::default(),
            term_reprs: Default::default(),
            writer,
            n_ff_sorts: 0,
            n_terms: 0,
        }
    }

    fn declare_sorts(&mut self, t: Term) {
        for sub_t in PostOrderIter::new(t) {
            let s = check(&sub_t);
            match &s {
                Sort::Field(f) => {
                    if !self.sort_reprs.contains_key(&s) {
                        let name = format!("FF{}", self.n_ff_sorts);
                        writeln!(
                            self.writer,
                            "(define-sort {} () (_ FiniteField {}))",
                            name,
                            f.modulus()
                        )
                        .unwrap();
                        self.sort_reprs.insert(s, name);
                        self.n_ff_sorts += 1;
                    }
                }
                Sort::BitVector(w) => {
                    let name = format!("(_ BitVec {})", w);
                    self.sort_reprs.insert(s, name);
                }
                Sort::Int => {
                    self.sort_reprs.insert(s, "Int".into());
                }
                Sort::Bool => {
                    self.sort_reprs.insert(s, "Bool".into());
                }
                _ => unimplemented!("sort {}", s),
            }
        }
    }

    fn declare_vars(&mut self, t: Term) {
        for sub_t in PostOrderIter::new(t) {
            if let Op::Var(name, sort) = &sub_t.op {
                writeln!(
                    &mut self.writer,
                    "(declare-fun {} () {})",
                    name,
                    self.sort_reprs.get(sort).unwrap()
                )
                .unwrap();
            }
        }
    }

    fn write_term(&mut self, t: Term) {
        let mut close = 0;
        for sub_t in PostOrderIter::new(t.clone()) {
            let name = format!("let{}", self.n_terms);
            self.n_terms += 1;
            let op: Option<String> = match &sub_t.op {
                &PF_ADD => Some("ff.add".into()),
                &PF_MUL => Some("ff.mul".into()),
                &PF_NEG => Some("ff.neg".into()),
                Op::Const(Value::Field(f)) => {
                    let s = check(&sub_t);
                    Some(format!(
                        "(as ff{} {})",
                        f.i(),
                        self.sort_reprs.get(&s).unwrap()
                    ))
                }
                &INT_MUL => Some("*".into()),
                &INT_ADD => Some("+".into()),
                Op::BoolNaryOp(_)
                | Op::Const(Value::Bool(_))
                | Op::Implies
                | Op::Not
                | Op::Const(Value::Int(_))
                | Op::IntBinPred(_)
                | Op::Const(Value::BitVector(_))
                | Op::BvBinOp(_)
                | Op::BvBinPred(_)
                | Op::BvNaryOp(_)
                | Op::BvUnOp(_)
                | Op::Var(..)
                | Op::Ite
                | Op::Eq => Some(format!("{}", sub_t.op)),
                _ => unimplemented!("op in term: {}", sub_t),
            };
            if let Some(op) = op {
                close += 1;
                if sub_t.op.arity() == Some(0) {
                    writeln!(&mut self.writer, "  (let (({} {}))", name, op).unwrap();
                } else {
                    write!(&mut self.writer, "  (let (({} ({}", name, op).unwrap();
                    for c in &sub_t.cs {
                        write!(&mut self.writer, " {}", self.term_reprs.get(c).unwrap()).unwrap();
                    }
                    writeln!(&mut self.writer, ")))").unwrap();
                }
            }
            self.term_reprs.insert(sub_t.clone(), name);
        }
        writeln!(&mut self.writer, "  {}", self.term_reprs.get(&t).unwrap()).unwrap();
        for _ in 0..close {
            write!(&mut self.writer, ")").unwrap();
        }
        writeln!(&mut self.writer, "").unwrap();
    }

    fn write_query(&mut self, t: &Term) {
        writeln!(&mut self.writer, "(set-info :smt-lib-version 2.6)").unwrap();
        writeln!(&mut self.writer, "(set-info :category \"crafted\")").unwrap();
        writeln!(
            &mut self.writer,
            "(set-logic {})",
            get_logic_string(t.clone())
        )
        .unwrap();
        self.declare_sorts(t.clone());
        self.declare_vars(t.clone());
        writeln!(&mut self.writer, "(assert ",).unwrap();
        self.write_term(t.clone());
        writeln!(&mut self.writer, ")").unwrap();
        writeln!(&mut self.writer, "(check-sat)").unwrap();
    }
}

pub fn write_query<W: Write>(w: &mut W, t: &Term) {
    let mut p = Printer::new(w);
    p.write_query(t);
}
