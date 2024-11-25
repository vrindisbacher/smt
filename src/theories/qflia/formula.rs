use crate::theories::formula::SMTFormula;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr<T: Debug + Hash + PartialEq + Eq> {
    Atom(Int<T>),
    Mul(i128, Box<Expr<T>>),
    Add(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T: Debug + Hash + PartialEq + Eq> Expr<T> {
    pub(crate) fn distribute(self, int: i128) -> Self {
        match self {
            Expr::Atom(atm) => match atm {
                Int::Const(x) => Expr::Atom(Int::Const(x * int)),
                Int::Var(v) => Expr::Mul(int, Box::new(Expr::Atom(Int::Var(v)))),
            },
            Expr::Mul(i, expr) => expr.distribute(int * i),
            Expr::Add(lhs, rhs) => {
                Expr::Add(Box::new(lhs.distribute(int)), Box::new(rhs.distribute(int)))
            }
        }
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct QFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    // alway <=
    // lhs <= rhs => lhs - rhs <= 0
    pub expr: Expr<T>,
}

pub trait IntoExpr<T: Debug + Hash + PartialEq + Eq> {
    fn into_expr(self) -> Expr<T>;
}

pub trait QFLIAOp<T: Debug + Clone + Hash + PartialEq + Eq>: IntoExpr<T> + Sized {
    fn add(self, rhs: impl IntoExpr<T>) -> Expr<T> {
        Expr::Add(Box::new(self.into_expr()), Box::new(rhs.into_expr()))
    }

    fn sub(self, rhs: impl IntoExpr<T>) -> Expr<T> {
        // turns x - y into x + (-y)
        Expr::Add(
            Box::new(self.into_expr()),
            Box::new(Int::from_const(-1).mul(rhs.into_expr())),
        )
    }

    fn gte(self, rhs: impl IntoExpr<T>) -> SMTFormula<QFLIAFormula<T>> {
        // normalized so that we are always comparing to 0
        // x >= y = -x <= -y = -x + y <= 0
        SMTFormula::Atom(QFLIAFormula {
            expr: Int::from_const(-1)
                .mul(self.into_expr())
                .add(rhs.into_expr()),
        })
    }

    fn lte(self, rhs: impl IntoExpr<T>) -> SMTFormula<QFLIAFormula<T>> {
        // normalized so that we are always comparing to 0
        SMTFormula::Atom(QFLIAFormula {
            expr: self.into_expr().sub(rhs.into_expr()),
        })
    }

    fn gt(self, rhs: impl IntoExpr<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns gt into not ( lte ) and makes sure we compare to zero
        self.into_expr().lte(rhs.into_expr()).not()
    }

    fn lt(self, rhs: impl IntoExpr<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns lt into not ( gte )
        self.into_expr().gte(rhs.into_expr()).not()
    }

    fn eq(self, rhs: impl IntoExpr<T> + Clone) -> SMTFormula<QFLIAFormula<T>> {
        // turns eq into gte && lte
        let lhs = self.into_expr();
        let rhs = rhs.into_expr();
        lhs.clone().gte(rhs.clone()).and(lhs.lte(rhs))
    }

    fn neq(self, rhs: impl IntoExpr<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns neq into gt && lt
        let lhs = self.into_expr();
        let rhs = rhs.into_expr();
        lhs.clone().gt(rhs.clone()).and(lhs.lt(rhs))
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> IntoExpr<T> for Expr<T> {
    fn into_expr(self) -> Expr<T> {
        self
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> QFLIAOp<T> for Expr<T> {}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Int<T: Debug + Hash + PartialEq + Eq> {
    // a linear constant is one with an actual value
    Const(i128),
    // a variable is an abstract value over some name of type T, for example Int("x")
    Var(T),
}

impl<T: Debug + Hash + PartialEq + Eq> Int<T> {
    pub fn from_const(val: i128) -> Self {
        Int::Const(val)
    }

    pub fn from_var(val: T) -> Self {
        Int::Var(val)
    }

    //
    // mul
    //
    // implemented only for ints because
    // qflia formula's must be of the form r * a where r = rational
    // and a is a linear term
    //
    // Restricting mul to Int::from_const(3).mul(Int::from_var(x).add(Int::from_var(y)))
    // does this.
    pub fn mul(self, rhs: impl IntoExpr<T>) -> Expr<T> {
        match self {
            Int::Const(i) => Expr::Mul(i, Box::new(rhs.into_expr())),
            Int::Var(_) => panic!("Multiplication in linear formulas must be by constant"),
        }
    }
}

impl<T: Debug + Hash + PartialEq + Eq> IntoExpr<T> for Int<T> {
    fn into_expr(self) -> Expr<T> {
        Expr::Atom(self)
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> QFLIAOp<T> for Int<T> {}
