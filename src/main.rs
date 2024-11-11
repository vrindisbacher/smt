use std::collections::HashMap;

use sat::{
    defs::{Clause, Formula, Var},
    dpll::Solver,
};

mod sat;

fn main() {
    let var1 = Var::new("a");
    let var1_neg = Var::negated("a");
    let var2 = Var::new("b");
    let clause1 = Clause::new(vec![var1]);
    let clause2 = Clause::new(vec![var1_neg, var2]);
    let formula = Formula::new(vec![clause1, clause2]);
    let res = Solver::new(formula).run();
    println!("{res:?}");
}
