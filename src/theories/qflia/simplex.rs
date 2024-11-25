use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::formula::{BinaryOp, Expr, Int, QFLIAFormula};

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

    fn parse_expr(&mut self, expr: &'var Expr<T>) {
        match expr {
            Expr::Atom(int) => match int {
                Int::Const(_x) => {
                    // not sure what to do
                }
                Int::Var(v) => {
                    // insert var
                    self.vars.insert(v);
                }
            },
            Expr::BinExpr(lhs, rhs, op) => match op {
                BinaryOp::Add => {
                    self.parse_expr(lhs);
                    self.parse_expr(rhs);
                }
                BinaryOp::Mul => {
                    self.parse_expr(lhs);
                    self.parse_expr(rhs);
                }
            },
        }
    }

    pub fn parse_qflia(&mut self, formula: &'var QFLIAFormula<T>) -> LinearConstraint {
        self.parse_expr(&formula.expr);
        todo!()
    }
}
