use structopt::StructOpt;

use rand::{distributions::Distribution, distributions::WeightedIndex, seq::SliceRandom};
use rand_distr::Geometric;

use std::collections::HashMap;
use std::fmt::Write;

use circ::ir::term::*;
use circ::term;
use circ_fields::FieldT;

#[derive(Debug, StructOpt)]
#[structopt(
    name = "bench_gen",
    about = "Generate SMT2 benchmarks related to ff compilations of boolean computations"
)]
struct Options {
    #[structopt(long, help = "Number of non-variable terms in the computation")]
    terms: usize,
    #[structopt(long, help = "Number of variables")]
    vars: usize,
    #[structopt(
        long,
        default_value = "0.7",
        help = "Probability of adding an extra argument to an n-ary operator"
    )]
    nary_arg_geo_param: f64,
    #[structopt(long, help = "Omit constant terms (true and false)")]
    no_consts: bool,
    #[structopt(
        long,
        help = "Try to break compilation, e.g., by dropping a constraint"
    )]
    try_break: bool,
    #[structopt(
        short = "o",
        long,
        help = "Operators to omit. Options: => not ite and or xor ="
    )]
    omit_ops: Vec<String>,
}

impl Options {
    fn sample_bool_term(&self) -> Term {
        // (uses, generation number, term)
        let mut terms = Vec::new();
        terms.extend(
            variable_names()
                .take(self.vars)
                .enumerate()
                .map(|(i, n)| (0, i, leaf_term(Op::Var(n, Sort::Bool)))),
        );
        if !self.no_consts {
            terms.push((0, terms.len(), leaf_term(Op::Const(Value::Bool(true)))));
            terms.push((0, terms.len(), leaf_term(Op::Const(Value::Bool(false)))));
        }
        let rng = &mut rand::thread_rng();
        let nary_arity_dist = Geometric::new(1.0 - self.nary_arg_geo_param).unwrap();
        let mut ops = vec![IMPLIES, NOT, XOR, AND, OR, EQ, ITE];
        ops.retain(|o| !self.omit_ops.contains(&format!("{}", o)));
        for _ in 0..(self.terms - 1) {
            let op = ops.choose(rng).unwrap().clone();
            let arity = op.arity();
            let n_args = arity.unwrap_or_else(|| 2 + nary_arity_dist.sample(rng) as usize);
            let mut args = Vec::new();
            for _ in 0..n_args {
                let mut terms_cp = terms.clone();
                let n = terms.len();
                terms_cp.sort();
                let weights: Vec<usize> = (0..n).map(|i| (n - i) * (n - i)).collect();
                let choice = WeightedIndex::new(&weights).unwrap().sample(rng);
                let (_, i, t) = terms_cp[choice].clone();
                args.push(t);
                terms[i].0 += 1;
            }
            terms.push((0, terms.len(), term(op, args)));
        }
        let mut nary_ops = vec![XOR, AND, OR];
        nary_ops.retain(|o| !self.omit_ops.contains(&format!("{}", o)));
        let op = nary_ops.choose(rng).unwrap().clone();
        term(
            op,
            terms
                .into_iter()
                .filter(|i| i.0 == 0)
                .map(|i| i.2)
                .collect(),
        )
    }
}

fn variable_names() -> impl Iterator<Item = String> {
    let mut i: usize = 0;
    std::iter::repeat_with(move || {
        let n_reps = i / 26;
        let out = String::from_utf8(vec![b'a' + (i % 26) as u8; n_reps + 1]).unwrap();
        i += 1;
        out
    })
}

struct CompilerOutput {
    bool_vars_to_ff_vars: HashMap<String, String>,
    output_var: String,
    assertion: Term,
}

trait Compiler {
    fn compile(bool_term: &Term, field: &FieldT, try_break: bool) -> CompilerOutput;

    /// Generate a term that is SAT when the compilation is unsound.
    ///
    /// ## Arguments
    ///
    /// * `bool_term`: the term to compile
    /// * `field`: the field to compile it in
    /// * `try_break`: whether to try to break compilation, e.g. by omitting a constraint
    fn generate(bool_term: &Term, field: &FieldT, try_break: bool) -> Term {
        let o = Self::compile(bool_term, field, try_break);
        let inputs_are_encoded = term(
            AND,
            o.bool_vars_to_ff_vars
                .iter()
                .map(|(bv, ffv)| {
                    let bv = leaf_term(Op::Var(bv.clone(), Sort::Bool));
                    let ffv = leaf_term(Op::Var(ffv.clone(), Sort::Field(field.clone())));
                    term!(EQ; ffv, term(ITE, vec![bv, pf_lit(field.new_v(1)), pf_lit(field.zero())]))
                })
                .collect(),
        );
        let output = leaf_term(Op::Var(o.output_var.clone(), Sort::Field(field.clone())));
        let output_is_boolean = term!(
            OR;
            term(EQ, vec![pf_lit(field.new_v(1)), output.clone()]),
            term(EQ, vec![pf_lit(field.zero()), output.clone()])
        );
        let output_as_bool = term(EQ, vec![pf_lit(field.new_v(1)), output]);
        let output_agrees = term(EQ, vec![output_as_bool, bool_term.clone()]);
        term!(NOT;
            term!(IMPLIES;
                term(AND, vec![inputs_are_encoded, o.assertion]),
                term(AND, vec![output_is_boolean, output_agrees])
            )
        )
    }
}

mod zok {
    use super::*;

    pub struct ZokReferenceCompiler;

    impl Compiler for ZokReferenceCompiler {
        fn compile(t: &Term, field: &FieldT, try_break: bool) -> CompilerOutput {
            std::fs::write("z.zok", zok::zok_code(&t)).unwrap();
            std::process::Command::new("zokrates")
                .args(["compile", "-i", "z.zok", "-o", "out"])
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
            std::process::Command::new("zokrates")
                .args(["inspect", "-i", "out", "--ztf"])
                .spawn()
                .unwrap()
                .wait()
                .unwrap();
            let mut vars: Vec<String> = extras::free_variables(t.clone()).into_iter().collect();
            vars.sort();
            let (ff_inputs, ff_assert, ff_ret) = zok::parse_ztf("out.ztf", field, try_break);
            CompilerOutput {
                bool_vars_to_ff_vars: vars.into_iter().zip(ff_inputs).collect(),
                output_var: ff_ret,
                assertion: ff_assert,
            }
        }
    }

    pub fn zok_code(t: &Term) -> String {
        let mut out = String::new();
        let mut vars: Vec<String> = extras::free_variables(t.clone()).into_iter().collect();
        vars.sort();
        write!(&mut out, "def main(").unwrap();
        let mut i = 0;
        for v in &vars {
            i += 1;
            if i == 1 {
                write!(&mut out, "bool {}", v).unwrap();
            } else {
                write!(&mut out, ", bool {}", v).unwrap();
            }
        }
        writeln!(&mut out, ") -> bool:").unwrap();
        let mut names: TermMap<String> = TermMap::new();
        let mut i = 0;
        for t in PostOrderIter::new(t.clone()) {
            let get = |i: usize| names.get(&t.cs[i]).unwrap();
            let expr = match &t.op {
                Op::Var(name, _) => name.clone(),
                Op::Const(..) => format!("{}", t),
                Op::Implies => format!("!{} || {}", get(0), get(1)),
                Op::Eq => format!("{} == {}", get(0), get(1)),
                Op::Not => format!("!{}", get(0)),
                Op::Ite => format!("if {} then {} else {} fi", get(0), get(1), get(2)),
                Op::BoolNaryOp(BoolNaryOp::Or) => {
                    let mut out = format!("{}", get(0));
                    for i in 1..t.cs.len() {
                        out += &format!(" || {}", get(i));
                    }
                    out
                }
                Op::BoolNaryOp(BoolNaryOp::And) => {
                    let mut out = format!("{}", get(0));
                    for i in 1..t.cs.len() {
                        out += &format!(" && {}", get(i));
                    }
                    out
                }
                Op::BoolNaryOp(BoolNaryOp::Xor) => {
                    let mut out = format!("{}", get(0));
                    for i in 1..t.cs.len() {
                        out += &format!(" ^ {}", get(i));
                    }
                    out
                }
                _ => unreachable!("op {}", t.op),
            };
            let name = format!("let{}", i);
            i += 1;
            writeln!(&mut out, "  bool {} = {}", name, expr).unwrap();
            names.insert(t.clone(), name);
        }
        writeln!(&mut out, "  return let{}", i - 1).unwrap();
        out
    }

    trait VCollect: Iterator + Sized {
        fn vcollect(self) -> Vec<<Self as Iterator>::Item> {
            self.collect()
        }
    }

    impl<I: Iterator> VCollect for I {}

    fn parse_var(s: &str, field: &FieldT) -> Term {
        match s {
            "~out_0" => leaf_term(Op::Var("out".into(), Sort::Field(field.clone()))),
            "~one" => pf_lit(field.new_v(1)),
            _ => leaf_term(Op::Var(s.into(), Sort::Field(field.clone()))),
        }
    }

    fn parse_const(mut s: &str, field: &FieldT) -> Term {
        s = s.trim_matches('(').trim_matches(')');
        let i = rug::Integer::from_str_radix(s, 10).unwrap();
        pf_lit(field.new_v(i))
    }

    fn parse_lc_term(s: &str, field: &FieldT) -> Term {
        let toks = s.split(" * ").vcollect();
        assert!(toks.len() == 2, "{}", s);
        term(
            PF_MUL,
            vec![parse_const(&toks[0], field), parse_var(&toks[1], field)],
        )
    }

    fn parse_lc(s: &str, field: &FieldT) -> Term {
        if s == "0" {
            pf_lit(field.zero())
        } else {
            term(
                PF_ADD,
                s.split(" + ").map(|t| parse_lc_term(t, field)).collect(),
            )
        }
    }

    fn parse_constraint(mut s: &str, field: &FieldT) -> Term {
        s = s.trim();
        let lc_a = parse_lc(&s.split(") * (").next().unwrap()[1..], field);
        let lc_b = parse_lc(
            s.split(") * (")
                .nth(1)
                .unwrap()
                .split(") ==")
                .next()
                .unwrap(),
            field,
        );
        let lc_c = parse_lc(s.split(") == ").nth(1).unwrap(), field);
        term(EQ, vec![term(PF_MUL, vec![lc_a, lc_b]), lc_c])
    }

    /// Returns (ff input variables, assertion term, ff output variable)
    pub fn parse_ztf(path: &str, field: &FieldT, drop_final: bool) -> (Vec<String>, Term, String) {
        let contents = std::fs::read_to_string(path).unwrap();
        let mut lines = contents.lines().vcollect();
        lines.reverse();
        assert!(lines.pop().unwrap().starts_with("# curve:"));
        assert!(lines.pop().unwrap().starts_with("# constraint_count:"));
        let header_line = lines.pop().unwrap();
        assert!(header_line.starts_with("def main"));
        let header_toks = header_line.split(&['(', ')']).vcollect();
        let vars = header_toks[1].split(", ").map(String::from).vcollect();
        let mut constraints = Vec::new();
        while let Some(l) = lines.pop() {
            if !(l.trim().starts_with("return") || l.trim().starts_with('#')) {
                constraints.push(parse_constraint(l, field));
            }
        }
        if drop_final {
            constraints.pop();
        }
        (vars, term(AND, constraints), "out".into())
    }
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::from_args();
    let t = opts.sample_bool_term();
    let formula = zok::ZokReferenceCompiler::generate(&t, &FieldT::FBls12381, opts.try_break);
    let formula = circ::ir::opt::cfold::fold(&formula, &[]);
    println!("{}", text::serialize_term(&formula));
    let f = std::fs::File::create("out.smt2").unwrap();
    circ::target::smt::write_smt2(f, &formula);
}
