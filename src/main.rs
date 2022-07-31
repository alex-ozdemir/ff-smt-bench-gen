use rand::{
    distributions::Distribution, distributions::WeightedIndex, seq::SliceRandom, SeedableRng,
};
use rand_distr::Geometric;
use rug::Integer;
use structopt::clap::arg_enum;
use structopt::StructOpt;

use std::collections::HashMap;
use std::fmt::Write;
use std::sync::Arc;
use std::time::{Duration, Instant};

use circ::front::FrontEnd;
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
        help = "Prob. of adding an extra argument to an n-ary operator"
    )]
    nary_arg_geo_param: f64,
    #[structopt(long, help = "Omit constant terms (true and false)")]
    no_consts: bool,
    #[structopt(
        long,
        help = "Try to break compilation, e.g., by dropping a constraint"
    )]
    try_break: bool,
    #[structopt(long, help = "Enable CirC optimizations")]
    circ_opt: bool,
    #[structopt(
        long,
        default_value = "255",
        help = "How many bits in the field. Uses the first prime in that range, or, for 255 bits, Bls12-381's scalar field"
    )]
    field_bits: u16,
    #[structopt(short = "o", long, help = "Operators to omit: => not ite and or xor =")]
    omit_ops: Vec<String>,
    #[structopt(
        short = "t",
        long,
        help = "Toolchain to use",
        default_value = "ZokCirC"
    )]
    toolchain: Toolchain,
    #[structopt(long, help = "Logic to use", default_value = "FF")]
    logic: Logic,
    #[structopt(long, help = "for random generation")]
    seed: Option<u64>,
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum Toolchain {
        ZokRef,
        ZokCirC,
        CirC,
    }
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    enum Logic {
        FF,
        BV,
        NIA,
        PureFf,
    }
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
        let mut rng = rand::rngs::StdRng::from_entropy();
        if let Some(s) = self.seed {
            rng = rand::rngs::StdRng::seed_from_u64(s);
        }
        let nary_arity_dist = Geometric::new(1.0 - self.nary_arg_geo_param).unwrap();
        let mut ops = vec![IMPLIES, NOT, XOR, AND, OR, EQ, ITE];
        ops.retain(|o| !self.omit_ops.contains(&format!("{}", o)));
        for _ in 0..(self.terms - 1) {
            let op = ops.choose(&mut rng).unwrap().clone();
            let arity = op.arity();
            let n_args = arity.unwrap_or_else(|| 2 + nary_arity_dist.sample(&mut rng) as usize);
            let mut args = Vec::new();
            for _ in 0..n_args {
                let mut terms_cp = terms.clone();
                let n = terms.len();
                terms_cp.sort();
                let weights: Vec<usize> = (0..n).map(|i| (n - i) * (n - i)).collect();
                let choice = WeightedIndex::new(&weights).unwrap().sample(&mut rng);
                let (_, i, t) = terms_cp[choice].clone();
                args.push(t);
                terms[i].0 += 1;
            }
            terms.push((0, terms.len(), term(op, args)));
        }
        let mut nary_ops = vec![XOR, AND, OR];
        nary_ops.retain(|o| !self.omit_ops.contains(&format!("{}", o)));
        let op = nary_ops.choose(&mut rng).unwrap().clone();
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
    constraints: usize,
}

struct GeneratorOutput {
    should_be_unsat: Term,
    compile_time: Duration,
    constraints: usize,
}

trait Compiler {
    fn compile(&self, bool_term: &Term, field: &FieldT, try_break: bool) -> CompilerOutput;

    /// Generate a term that is SAT when the compilation is unsound.
    ///
    /// ## Arguments
    ///
    /// * `bool_term`: the term to compile
    /// * `field`: the field to compile it in
    /// * `try_break`: whether to try to break compilation, e.g. by omitting a constraint
    fn generate(&self, bool_term: &Term, field: &FieldT, try_break: bool) -> GeneratorOutput {
        let start = Instant::now();
        let o = self.compile(bool_term, field, try_break);
        let compile_time = start.elapsed();
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
        GeneratorOutput {
            should_be_unsat: term!(NOT;
                term!(IMPLIES;
                    term(AND, vec![inputs_are_encoded, o.assertion]),
                    term(AND, vec![output_is_boolean, output_agrees])
                )
            ),
            compile_time,
            constraints: o.constraints,
        }
    }
}

mod zok {
    use super::*;

    pub struct ZokRef;

    impl Compiler for ZokRef {
        fn compile(&self, t: &Term, field: &FieldT, try_break: bool) -> CompilerOutput {
            std::fs::write("z.zok", zok_code(&t)).unwrap();
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
            let (ff_inputs, ff_assert, ff_ret, constraints) =
                zok::parse_ztf("out.ztf", field, try_break);
            CompilerOutput {
                bool_vars_to_ff_vars: vars.into_iter().zip(ff_inputs).collect(),
                output_var: ff_ret,
                assertion: ff_assert,
                constraints,
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
                write!(&mut out, "private bool {}", v).unwrap();
            } else {
                write!(&mut out, ", private bool {}", v).unwrap();
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
    pub fn parse_ztf(
        path: &str,
        field: &FieldT,
        drop_final: bool,
    ) -> (Vec<String>, Term, String, usize) {
        let contents = std::fs::read_to_string(path).unwrap();
        let mut lines = contents.lines().vcollect();
        lines.reverse();
        assert!(lines.pop().unwrap().starts_with("# curve:"));
        assert!(lines.pop().unwrap().starts_with("# constraint_count:"));
        let header_line = lines.pop().unwrap();
        assert!(header_line.starts_with("def main"));
        let header_toks = header_line.split(&['(', ')']).vcollect();
        let vars = header_toks[1]
            .split(", ")
            .map(|s| s.trim_start_matches("private ").into())
            .vcollect();
        let mut constraints = Vec::new();
        while let Some(l) = lines.pop() {
            if !(l.trim().starts_with("return") || l.trim().starts_with('#')) {
                constraints.push(parse_constraint(l, field));
            }
        }
        let n = constraints.len();
        if drop_final {
            constraints.pop();
        }
        (vars, term(AND, constraints), "out".into(), n)
    }
}

mod circ_ {
    use super::*;

    pub struct CirC(pub bool);
    impl Compiler for CirC {
        fn compile(&self, bool_term: &Term, field: &FieldT, try_break: bool) -> CompilerOutput {
            let is_right =
                term![EQ; bool_term.clone(), leaf_term(Op::Var("return".into(), Sort::Bool))];
            let mut c = Computation::default();
            for v in extras::free_variables(is_right.clone()) {
                c.new_var(
                    &v,
                    Sort::Bool,
                    if v == "return" {
                        None
                    } else {
                        Some(circ::ir::proof::PROVER_ID)
                    },
                    None,
                );
            }
            c.outputs.push(is_right);
            let c = if self.0 {
                c
            } else {
                use circ::ir::opt::Opt;
                circ::ir::opt::opt(
                    c,
                    vec![
                        Opt::ScalarizeVars,
                        Opt::Flatten,
                        Opt::Sha,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Flatten,
                        Opt::Inline,
                        // Tuples must be eliminated before oblivious array elim
                        Opt::Tuple,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Obliv,
                        // The obliv elim pass produces more tuples, that must be eliminated
                        Opt::Tuple,
                        Opt::LinearScan,
                        // The linear scan pass produces more tuples, that must be eliminated
                        Opt::Tuple,
                        Opt::Flatten,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Inline,
                    ],
                )
            };
            let (r1cs, _, _) = circ::target::r1cs::trans::to_r1cs(c, field.clone());
            let r1cs = circ::target::r1cs::opt::reduce_linearities(r1cs, Some(50));
            let constraints = r1cs.constraints().len();
            let r1cs_term = r1cs.ir_term();
            let bool_vars = extras::free_variables(bool_term.clone());
            let base_vars_to_r1cs_vars: HashMap<String, String> =
                extras::free_variables(r1cs_term.clone())
                    .into_iter()
                    .map(|r1csv| (r1cs_var_name_to_orig_var_name(&r1csv), r1csv))
                    .filter(|(b, _)| bool_vars.contains(b))
                    .collect();
            let output_var = extras::free_variables(r1cs_term.clone())
                .into_iter()
                .find(|v| r1cs_var_name_to_orig_var_name(v) == "return")
                .unwrap();
            let assertion = if try_break {
                match &r1cs_term.op {
                    &AND if r1cs_term.cs.len() > 1 => term(
                        AND,
                        r1cs_term
                            .cs
                            .iter()
                            .take(r1cs_term.cs.len() - 1)
                            .cloned()
                            .collect(),
                    ),
                    _ => r1cs_term,
                }
            } else {
                r1cs_term
            };
            CompilerOutput {
                bool_vars_to_ff_vars: base_vars_to_r1cs_vars,
                output_var,
                assertion,
                constraints,
            }
        }
    }

    fn r1cs_var_name_to_orig_var_name(r1cs_var_name: &str) -> String {
        let i = r1cs_var_name.rfind('_').unwrap();
        r1cs_var_name[..i].into()
    }

    pub struct CirCZok(pub bool);
    impl Compiler for CirCZok {
        fn compile(&self, bool_term: &Term, field: &FieldT, try_break: bool) -> CompilerOutput {
            if std::env::var("ZSHARP_STDLIB_PATH").is_err() {
                eprintln!("Warning: ZSHARP_STDLIB_PATH is not set. This may cause an error.");
            }
            std::fs::write("z.zok", zok::zok_code(&bool_term)).unwrap();
            let inputs = circ::front::zsharp::Inputs {
                file: "z.zok".into(),
                mode: circ::front::Mode::Proof,
                isolate_asserts: false,
            };
            let c = circ::front::zsharp::ZSharpFE::gen(inputs);
            let c = if self.0 {
                c
            } else {
                use circ::ir::opt::Opt;
                circ::ir::opt::opt(
                    c,
                    vec![
                        Opt::ScalarizeVars,
                        Opt::Flatten,
                        Opt::Sha,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Flatten,
                        Opt::Inline,
                        // Tuples must be eliminated before oblivious array elim
                        Opt::Tuple,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Obliv,
                        // The obliv elim pass produces more tuples, that must be eliminated
                        Opt::Tuple,
                        Opt::LinearScan,
                        // The linear scan pass produces more tuples, that must be eliminated
                        Opt::Tuple,
                        Opt::Flatten,
                        Opt::ConstantFold(Box::new([])),
                        Opt::Inline,
                    ],
                )
            };
            let (r1cs, _, _) = circ::target::r1cs::trans::to_r1cs(c, field.clone());
            let r1cs = circ::target::r1cs::opt::reduce_linearities(r1cs, Some(50));
            let constraints = r1cs.constraints().len();
            let r1cs_term = r1cs.ir_term();
            let bool_vars = extras::free_variables(bool_term.clone());
            let base_vars_to_r1cs_vars: HashMap<String, String> =
                extras::free_variables(r1cs_term.clone())
                    .into_iter()
                    .map(|r1csv| (r1cs_var_name_to_orig_var_name(&r1csv), r1csv))
                    .filter(|(b, _)| bool_vars.contains(b))
                    .collect();
            let output_var = extras::free_variables(r1cs_term.clone())
                .into_iter()
                .find(|v| r1cs_var_name_to_orig_var_name(v) == "return")
                .unwrap();
            let assertion = if try_break {
                match &r1cs_term.op {
                    &AND if r1cs_term.cs.len() > 1 => term(
                        AND,
                        r1cs_term
                            .cs
                            .iter()
                            .take(r1cs_term.cs.len() - 1)
                            .cloned()
                            .collect(),
                    ),
                    _ => r1cs_term,
                }
            } else {
                r1cs_term
            };
            CompilerOutput {
                bool_vars_to_ff_vars: base_vars_to_r1cs_vars,
                output_var,
                assertion,
                constraints,
            }
        }
    }
}

// Get the first prime field of `bits` bits.
// If bits is 255, gets Bls12-381's scalar field instead.
fn get_field(bits: u16) -> FieldT {
    assert!(bits >= 2, "The number of prime bits must be >=2");
    if bits == 255 {
        FieldT::FBls12381
    } else {
        let mut i = Integer::from(1u8);
        i <<= bits as u32 - 1;
        i -= 1;
        i.next_prime_mut();
        FieldT::IntField(Arc::new(i))
    }
}

// Convert all field terms to bit-vectors. Requires all field terms to have field `f`.
fn pf_to_bv(formula: Term, f: &FieldT) -> Term {
    let f_bits = f.modulus().significant_bits() as usize;
    let bv_sort = Sort::BitVector(2 * f_bits);
    let bv_modulus = bv_lit(f.modulus(), 2 * f_bits);
    let mut cache: TermMap<Term> = TermMap::new();
    let mut assertions = Vec::new();
    for t in PostOrderIter::new(formula.clone()) {
        let cs: Vec<Term> = t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect();
        let new = match &t.op {
            Op::Const(Value::Field(c)) => {
                assert_eq!(&c.ty(), f);
                bv_lit(c.i(), 2 * f_bits)
            }
            Op::Var(name, Sort::Field(this_f)) => {
                assert_eq!(this_f, f);
                let v = leaf_term(Op::Var(name.clone(), bv_sort.clone()));
                assertions.push(term![BV_ULT; v.clone(), bv_modulus.clone()]);
                v
            }
            Op::PfNaryOp(PfNaryOp::Add) => {
                term![BV_UREM; term(BV_ADD, cs), bv_modulus.clone()]
            }
            Op::PfNaryOp(PfNaryOp::Mul) => {
                let mut acc = cs[0].clone();
                for i in cs.into_iter().skip(1) {
                    acc = term![BV_UREM; term![BV_MUL; acc, i], bv_modulus.clone()];
                }
                acc
            }
            o => term(o.clone(), cs),
        };
        cache.insert(t.clone(), new);
    }
    assertions.push(cache.remove(&formula).unwrap());
    term(AND, assertions)
}

// Convert all field terms to integers. Requires all field terms to have field `f`.
fn pf_to_nia(formula: Term, f: &FieldT) -> Term {
    let int_modulus = leaf_term(Op::Const(Value::Int(f.modulus().clone())));
    let int_zero = leaf_term(Op::Const(Value::Int(Integer::new())));
    let mut quotient_i = 0;
    let mut remainder_i = 0;
    let mut assertions = Vec::new();
    let mut assertions2 = Vec::new();
    let mut normalize = |t: Term| {
        let q = leaf_term(Op::Var(format!("embed_q{}", quotient_i), Sort::Int));
        let r = leaf_term(Op::Var(format!("embed_r{}", remainder_i), Sort::Int));
        quotient_i += 1;
        remainder_i += 1;
        assertions.push(term![INT_GE; r.clone(), int_zero.clone()]);
        assertions.push(term![INT_LT; r.clone(), int_modulus.clone()]);
        assertions
            .push(term![EQ; t, term![INT_ADD; term![INT_MUL; q, int_modulus.clone()], r.clone()]]);
        r
    };
    let mut cache: TermMap<Term> = TermMap::new();
    for t in PostOrderIter::new(formula.clone()) {
        let cs: Vec<Term> = t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect();
        let new = match &t.op {
            Op::Const(Value::Field(c)) => {
                assert_eq!(&c.ty(), f);
                leaf_term(Op::Const(Value::Int(c.i().clone())))
            }
            Op::Var(name, Sort::Field(this_f)) => {
                assert_eq!(this_f, f);
                let v = leaf_term(Op::Var(name.clone(), Sort::Int));
                assertions2.push(term![INT_LT; v.clone(), int_modulus.clone()]);
                assertions2.push(term![INT_GE; v.clone(), int_zero.clone()]);
                v
            }
            Op::PfNaryOp(PfNaryOp::Add) => normalize(term(INT_ADD, cs)),
            Op::PfNaryOp(PfNaryOp::Mul) => normalize(term(INT_MUL, cs)),
            o => term(o.clone(), cs),
        };
        cache.insert(t.clone(), new);
    }
    assertions.extend(assertions2);
    assertions.push(cache.remove(&formula).unwrap());
    term(AND, assertions)
}

fn pf_bool_neg(t: Term) -> Term {
    if let Sort::Field(f) = check(&t) {
        term![PF_ADD; pf_lit(f.new_v(1)), term![PF_NEG; t]]
    } else {
        panic!()
    }
}

// Convert all boolean terms to the field.
fn bool_to_pf(formula: Term, f: &FieldT) -> Term {
    let f_sort = Sort::Field(f.clone());
    let mut cache: TermMap<Term> = TermMap::new();
    let mut assertions = Vec::new();
    let mut ct = 0;
    let mut fresh = || {
        let v = leaf_term(Op::Var(format!("embed_i{}", ct), f_sort.clone()));
        ct += 1;
        v
    };
    for t in PostOrderIter::new(formula.clone()) {
        let cs: Vec<Term> = t.cs.iter().map(|c| cache.get(c).unwrap().clone()).collect();
        let new = match &t.op {
            Op::Const(Value::Bool(b)) => pf_lit(f.new_v(*b as u8)),
            Op::Var(name, Sort::Bool) => {
                let v = leaf_term(Op::Var(name.clone(), f_sort.clone()));
                assertions.push(term![EQ; term![PF_MUL; v.clone(), v.clone()], v.clone()]);
                v
            }
            Op::BoolNaryOp(BoolNaryOp::And) => term(PF_MUL, cs),
            Op::BoolNaryOp(BoolNaryOp::Or) => {
                pf_bool_neg(term(PF_MUL, cs.into_iter().map(pf_bool_neg).collect()))
            }
            Op::BoolNaryOp(o) => {
                unimplemented!("{}", o)
            }
            Op::Implies => pf_bool_neg(term![PF_MUL; cs[0].clone(), pf_bool_neg(cs[1].clone())]),
            Op::Eq => {
                match check(&t.cs[0]) {
                    Sort::Bool => {
                        // 1 - x - y + 2 * xy
                        term![PF_ADD;
                            pf_lit(f.new_v(1)),
                            term![PF_NEG; cs[0].clone()],
                            term![PF_NEG; cs[1].clone()],
                            term![PF_MUL; pf_lit(f.new_v(2)), cs[0].clone(), cs[1].clone()]
                        ]
                    }
                    Sort::Field(ff) => {
                        assert_eq!(&ff, f);
                        // m (x - y) = 1 - r
                        // r (x - y) = 0
                        let m = fresh();
                        let r = fresh();
                        let d = term![PF_ADD; cs[0].clone(), term![PF_NEG; cs[1].clone()]];
                        assertions.push(term![EQ; term![PF_MUL; m.clone(), d.clone()], pf_bool_neg(r.clone())]);
                        assertions.push(
                            term![EQ; term![PF_MUL; r.clone(), d.clone()], pf_lit(f.new_v(0))],
                        );
                        r
                    }
                    _ => unimplemented!(),
                }
            }
            Op::Ite => {
                // 1 - x - y + 2 * xy
                term![PF_ADD;
                    cs[2].clone(),
                    term![PF_MUL;
                        cs[0].clone(),
                        term![PF_ADD;
                            cs[1].clone(),
                            term![PF_NEG; cs[2].clone()]]]]
            }
            Op::Not => pf_bool_neg(cs[0].clone()),
            o => term(o.clone(), cs),
        };
        cache.insert(t.clone(), new);
    }
    assertions.push(term![EQ; cache.remove(&formula).unwrap(), pf_lit(f.new_v(1))]);
    term(AND, assertions)
}

fn main() {
    env_logger::Builder::from_default_env()
        .format_level(false)
        .format_timestamp(None)
        .init();
    let opts = Options::from_args();
    let t = opts.sample_bool_term();
    let field = get_field(opts.field_bits);
    let gen = match opts.toolchain {
        Toolchain::ZokRef => zok::ZokRef.generate(&t, &field, opts.try_break),
        Toolchain::ZokCirC => circ_::CirCZok(opts.circ_opt).generate(&t, &field, opts.try_break),
        Toolchain::CirC => circ_::CirC(opts.circ_opt).generate(&t, &field, opts.try_break),
    };
    let formula = match opts.logic {
        Logic::FF => gen.should_be_unsat.clone(),
        Logic::BV => pf_to_bv(gen.should_be_unsat.clone(), &field),
        Logic::NIA => pf_to_nia(gen.should_be_unsat.clone(), &field),
        Logic::PureFf => bool_to_pf(gen.should_be_unsat.clone(), &field),
    };
    let opt_formula = circ::ir::opt::cfold::fold(&formula, &[]);
    println!("constraints: {}", gen.constraints);
    println!("comp   time: {}", gen.compile_time.as_secs_f64());
    let f = std::fs::File::create("out.smt2").unwrap();
    circ::target::smt::write_smt2(f, &opt_formula);
}