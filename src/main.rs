use sat::var::Var;
use theories::qflia::formula::{Int, QFLIAOp};

pub mod sat;
pub mod theories;

fn main() {
    let x = Var::new("x");
    let formula = Int::from_var(x)
        .add(Int::from_const(5).sub(Int::from_var(x)))
        .sub(Int::from_const(5));
    println!("{:?}", formula.simplify());
}
