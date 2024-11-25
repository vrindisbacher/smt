use crate::theories::formula::SMTFormula;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr<T: Debug + Hash + PartialEq + Eq> {
    Atom(Int<T>),
    Mul(i128, Box<Expr<T>>),
    Add(Box<Expr<T>>, Box<Expr<T>>),
}

impl<T: Debug + Hash + PartialEq + Eq> Expr<T> {
    fn distribute(self, int: i128) -> Self {
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

    fn collect_atoms<'a>(
        self,
        mut var_collector: HashMap<T, i128>,
        mut const_collector: i128,
    ) -> (HashMap<T, i128>, i128) {
        match self {
            Expr::Atom(x) => match x {
                Int::Const(i) => {
                    const_collector += i;
                    (var_collector, const_collector)
                }
                Int::Var(v) => {
                    var_collector
                        .entry(v)
                        .and_modify(|sum| *sum += 1)
                        .or_insert(1);
                    (var_collector, const_collector)
                }
            },
            Expr::Mul(x, expr) => {
                // because of calling simplify which calls distribute -> we can guarantee that
                // mul is right next to a var so we can just insert it
                match *expr {
                    Expr::Atom(Int::Var(name)) => {
                        var_collector
                            .entry(name)
                            .and_modify(|sum| *sum += x)
                            .or_insert(x);
                        (var_collector, const_collector)
                    }
                    _ => {
                        panic!("Unexpected value in mul after distributing")
                    }
                }
            }
            Expr::Add(lhs, rhs) => {
                let (var_collector, const_collector) =
                    lhs.collect_atoms(var_collector, const_collector);
                let (var_collector, const_collector) =
                    rhs.collect_atoms(var_collector, const_collector);
                (var_collector, const_collector)
            }
        }
    }

    fn combine_like_terms(self) -> Self {
        // idea -> store a bunch of pointers to atomic terms - which you can then combine
        // at this point, everything is already in the simplest form because we've distributed
        // all multiplication - we just have addition and we can use the commutative property
        // to simplify as we please
        let term_collector = HashMap::new();
        let const_collector = 0;
        let (term_collector, const_collapsed) = self.collect_atoms(term_collector, const_collector);
        // Basically this is guaranteed to be (Expr + const) so we can just fold everything into a
        // constant
        term_collector.into_iter().fold(
            Expr::Atom(Int::from_const(const_collapsed)),
            |acc, (term, coeff)| {
                if coeff == 0 {
                    acc
                } else if coeff == 1 {
                    Expr::Add(Box::new(acc), Box::new(Expr::Atom(Int::from_var(term))))
                } else {
                    Expr::Add(
                        Box::new(acc),
                        Box::new(Expr::Mul(coeff, Box::new(Expr::Atom(Int::from_var(term))))),
                    )
                }
            },
        )
    }

    pub fn simplify(self) -> Self {
        let new = self.distribute(1);
        new.combine_like_terms()
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
