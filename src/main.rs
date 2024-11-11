use sat::{
    defs::{Clause, Formula, Lit},
    dpll::Solver,
};

mod sat;

fn main() {
    let var1 = Lit::new("a");
    let var1_neg = Lit::negated("a");
    let var2 = Lit::new("b");
    let clause1 = Clause::new(vec![var1]);
    let clause2 = Clause::new(vec![var1_neg, var2]);
    let formula = Formula::new(vec![clause1, clause2]);
    let res = Solver::new(formula).run();
    println!("{res:?}");
}
