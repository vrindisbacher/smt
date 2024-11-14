use crate::sat::var::{Lit, Var};

fn example() {
    let vara = Var::new("a");
    let varb = Var::new("b");
    let a = Lit::pos(vara);
    let b = Lit::pos(varb);
    let clause = a.implies(b);
}
