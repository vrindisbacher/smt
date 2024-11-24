use crate::theories::formula::SMTFormula;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum QFLIAUnOp {
    Neg,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum QFLIABinOp {
    Add,
    Mul,
    Gte,
    Lte,
}

#[allow(private_interfaces)]
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum QFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    Atom(Int<T>),
    UnaryExpr(Box<QFLIAFormula<T>>, QFLIAUnOp),
    BinExpr(Box<QFLIAFormula<T>>, Box<QFLIAFormula<T>>, QFLIABinOp),
}

pub trait IntoQFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    fn into_qflia(self) -> QFLIAFormula<T>;
}

pub trait QFLIAOp<T: Debug + Clone + Hash + PartialEq + Eq>: IntoQFLIAFormula<T> + Sized {
    //
    // Note: We cannot construct invalid formulas because all
    // ops that return boolean expressions (i.e. not arithmetic)
    // return SMTFormulas, not QFLIA formulas
    //
    // Therefore, the invariant that arguments to functions like
    // add or sub are only arithmetic ops is automatically upheld
    // by the type system
    //

    fn add(self, rhs: impl IntoQFLIAFormula<T>) -> QFLIAFormula<T> {
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia()),
            QFLIABinOp::Add,
        )
    }

    fn sub(self, rhs: impl IntoQFLIAFormula<T>) -> QFLIAFormula<T> {
        // turns x - y into x + (-y)
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia().neg()),
            QFLIABinOp::Add,
        )
    }

    fn gte(self, rhs: impl IntoQFLIAFormula<T>) -> SMTFormula<QFLIAFormula<T>> {
        // normalized so that we are always comparing to 0
        SMTFormula::Atom(QFLIAFormula::BinExpr(
            Box::new(self.into_qflia().sub(rhs.into_qflia())),
            Box::new(Int::from_const(0).into_qflia()),
            QFLIABinOp::Gte,
        ))
    }

    fn lte(self, rhs: impl IntoQFLIAFormula<T>) -> SMTFormula<QFLIAFormula<T>> {
        // normalized so that we are always comparing to 0
        SMTFormula::Atom(QFLIAFormula::BinExpr(
            Box::new(self.into_qflia().sub(rhs.into_qflia())),
            Box::new(Int::from_const(0).into_qflia()),
            QFLIABinOp::Lte,
        ))
    }

    fn gt(self, rhs: impl IntoQFLIAFormula<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns gt into not ( lte ) and makes sure we compare to zero
        self.into_qflia().lte(rhs.into_qflia()).not()
    }

    fn lt(self, rhs: impl IntoQFLIAFormula<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns lt into not ( gte )
        self.into_qflia().gte(rhs.into_qflia()).not()
    }

    fn eq(self, rhs: impl IntoQFLIAFormula<T> + Clone) -> SMTFormula<QFLIAFormula<T>> {
        // turns eq into gte && lte
        let lhs = self.into_qflia();
        let rhs = rhs.into_qflia();
        lhs.clone().gte(rhs.clone()).and(lhs.lte(rhs))
    }

    fn neq(self, rhs: impl IntoQFLIAFormula<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns neq into gt && lt
        let lhs = self.into_qflia();
        let rhs = rhs.into_qflia();
        lhs.clone().gt(rhs.clone()).and(lhs.lt(rhs))
    }

    fn neg(self) -> QFLIAFormula<T> {
        QFLIAFormula::UnaryExpr(Box::new(self.into_qflia()), QFLIAUnOp::Neg)
    }
}

impl<T: Debug + Hash + PartialEq + Eq> IntoQFLIAFormula<T> for QFLIAFormula<T> {
    fn into_qflia(self) -> QFLIAFormula<T> {
        self
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> QFLIAOp<T> for QFLIAFormula<T> {}

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
    pub fn mul(self, rhs: impl IntoQFLIAFormula<T>) -> QFLIAFormula<T> {
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia()),
            QFLIABinOp::Mul,
        )
    }
}

impl<T: Debug + Hash + PartialEq + Eq> IntoQFLIAFormula<T> for Int<T> {
    fn into_qflia(self) -> QFLIAFormula<T> {
        QFLIAFormula::Atom(self)
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> QFLIAOp<T> for Int<T> {}
