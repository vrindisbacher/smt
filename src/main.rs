use sat::{
    clause::Clause,
    formula::Formula,
    var::{Lit, Var},
    Solver,
};

mod dimacs;
mod sat;

fn main() {
    let var_a = Var::new("a");
    let var = Lit::pos(var_a);
    let var_neg = Lit::neg(var_a);
    let clause = Clause::new(vec![var]);
    let clause_neg = Clause::new(vec![var_neg]);
    let formula = Formula::new(vec![clause, clause_neg]);
    assert_eq!(Solver::new(formula).run(), false)
}
