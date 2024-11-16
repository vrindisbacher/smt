use crate::theories::formula::{IntoSMT, SMTFormula, SMTOps};
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum QFLIAUnOp {
    Neg,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum QFLIABinOp {
    Add,
    Mul,
    Gte,
    Lte,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum QFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    Atom(Int<T>),
    UnaryExpr(Box<QFLIAFormula<T>>, QFLIAUnOp),
    BinExpr(Box<QFLIAFormula<T>>, Box<QFLIAFormula<T>>, QFLIABinOp),
}

pub trait IntoQFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    fn into_qflia(self) -> QFLIAFormula<T>;
}

pub trait ValidOperand<T: Debug + Hash + PartialEq + Eq> {
    fn ensure_bool(&self) -> bool;
    fn ensure_only_arith_ops(&self) -> bool;
}

pub trait QFLIAOp<T: Debug + Clone + Hash + PartialEq + Eq>:
    IntoQFLIAFormula<T> + ValidOperand<T> + Sized
{
    fn add(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> QFLIAFormula<T> {
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia()),
            QFLIABinOp::Add,
        )
    }

    fn sub(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> QFLIAFormula<T> {
        // turns x - y into x + (-y)
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia().neg()),
            QFLIABinOp::Add,
        )
    }

    fn mul(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> QFLIAFormula<T> {
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia()),
            Box::new(rhs.into_qflia()),
            QFLIABinOp::Mul,
        )
    }

    fn gte(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> QFLIAFormula<T> {
        // normalized so that we are always comparing to 0
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia().sub(rhs.into_qflia())),
            Box::new(Int::from_const(0).into_qflia()),
            QFLIABinOp::Gte,
        )
    }

    fn lte(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> QFLIAFormula<T> {
        // normalized so that we are always comparing to 0
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        QFLIAFormula::BinExpr(
            Box::new(self.into_qflia().sub(rhs.into_qflia())),
            Box::new(Int::from_const(0).into_qflia()),
            QFLIABinOp::Lte,
        )
    }

    fn gt(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> SMTFormula<QFLIAFormula<T>> {
        // returns
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        // turns gt into not ( lte ) and makes sure we compare to zero
        self.into_qflia().lte(rhs.into_qflia()).into_smt().not()
    }

    fn lt(self, rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>) -> SMTFormula<QFLIAFormula<T>> {
        // turns lt into not ( gte )
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        self.into_qflia().gte(rhs.into_qflia()).into_smt().not()
    }

    fn equals(
        self,
        rhs: impl IntoQFLIAFormula<T> + ValidOperand<T> + Clone,
    ) -> SMTFormula<QFLIAFormula<T>> {
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        // turns eq into gte && lte
        let lhs = self.into_qflia();
        let rhs = rhs.into_qflia();
        lhs.clone().gte(rhs.clone()).and(lhs.lte(rhs))
    }

    fn n_equals(
        self,
        rhs: impl IntoQFLIAFormula<T> + ValidOperand<T>,
    ) -> SMTFormula<QFLIAFormula<T>> {
        assert_eq!(rhs.ensure_only_arith_ops(), true);
        // turns neq into gt && lt
        let lhs = self.into_qflia();
        let rhs = rhs.into_qflia();
        lhs.clone().gt(rhs.clone()).and(lhs.lt(rhs))
    }

    fn neg(self) -> QFLIAFormula<T> {
        // self has to be only arith ops
        assert_eq!(self.ensure_only_arith_ops(), true);
        QFLIAFormula::UnaryExpr(Box::new(self.into_qflia()), QFLIAUnOp::Neg)
    }
}

impl<T: Debug + Hash + PartialEq + Eq> IntoQFLIAFormula<T> for QFLIAFormula<T> {
    fn into_qflia(self) -> QFLIAFormula<T> {
        self
    }
}

impl<T: Debug + Hash + PartialEq + Eq> ValidOperand<T> for QFLIAFormula<T> {
    fn ensure_only_arith_ops(&self) -> bool {
        match self {
            QFLIAFormula::Atom(_) => true,
            QFLIAFormula::UnaryExpr(expr, _) => expr.ensure_only_arith_ops(),
            QFLIAFormula::BinExpr(lhs, rhs, op) => match op {
                QFLIABinOp::Add | QFLIABinOp::Mul => {
                    lhs.ensure_only_arith_ops() && rhs.ensure_only_arith_ops()
                }
                _ => false,
            },
        }
    }

    fn ensure_bool(&self) -> bool {
        match self {
            QFLIAFormula::Atom(_) => false,
            QFLIAFormula::UnaryExpr(_, _) => false,
            QFLIAFormula::BinExpr(_, _, op) => match op {
                QFLIABinOp::Add | QFLIABinOp::Mul => false,
                QFLIABinOp::Gte | QFLIABinOp::Lte => true,
            },
        }
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
}

impl<T: Debug + Hash + PartialEq + Eq> IntoQFLIAFormula<T> for Int<T> {
    fn into_qflia(self) -> QFLIAFormula<T> {
        QFLIAFormula::Atom(self)
    }
}

impl<T: Debug + Hash + PartialEq + Eq> ValidOperand<T> for Int<T> {
    fn ensure_only_arith_ops(&self) -> bool {
        true
    }
    fn ensure_bool(&self) -> bool {
        false
    }
}

impl<T: Debug + Clone + Hash + PartialEq + Eq> QFLIAOp<T> for Int<T> {}
