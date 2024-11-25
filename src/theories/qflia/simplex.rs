use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use crate::theories::qflia::formula::QFLIABinOp;

use super::formula::{QFLIAFormula, QFLIAUnOp};

#[derive(Debug)]
pub(crate) struct LinearConstraint {
    coefficients: HashMap<String, i32>, // Coefficients for each variable
    rhs: i32,                           // Right-hand side of the equation
}

#[derive(Debug)]
pub(crate) struct Simplex<'var, T: Debug + Hash + PartialEq + Eq> {
    constraints: Vec<LinearConstraint>, // all constraints for a given formula
    vars: HashSet<&'var T>,             // all variables in the formula
}

impl<'var, T: Debug + Hash + PartialEq + Eq> Simplex<'var, T> {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
            vars: HashSet::new(),
        }
    }

    fn parse_well_formed_side(&mut self, formula: &'var QFLIAFormula<T>) {
        match formula {
            QFLIAFormula::Atom(int) => match int {
                super::formula::Int::Const(val) => {
                    // a constant
                }
                super::formula::Int::Var(var) => {
                    // insert this into vars
                    self.vars.insert(var);
                }
            },
            QFLIAFormula::UnaryExpr(expr, op) => match op {
                QFLIAUnOp::Neg => todo!(),
            },
            QFLIAFormula::BinExpr(lhs, rhs, op) => match op {
                QFLIABinOp::Add => todo!(),
                QFLIABinOp::Mul => todo!(),
                QFLIABinOp::Gte | QFLIABinOp::Lte => {
                    panic!("Expected this to be unreachable. The qflia formula is ill formed")
                }
            },
        }
    }

    fn from_qflia(&mut self, formula: &'var QFLIAFormula<T>) -> LinearConstraint {
        // The QFLIA formula has to be _ <= _ or _ >= _
        // This is upheld by the sorts of formulas that the
        // SMT solver can take (SMTFormulas)
        // and the types that QFLIA formula operators yield.
        match formula {
            QFLIAFormula::BinExpr(lhs, rhs, QFLIABinOp::Gte) => {}
            QFLIAFormula::BinExpr(lhs, rhs, QFLIABinOp::Lte) => {}
            _ => panic!("Expected this to be unreachable. Received invalid formula - expected _ <= _ or _ >= _"),
        }
        todo!()
    }
}
