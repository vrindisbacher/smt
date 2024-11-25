use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::formula::{Expr, Int, QFLIAFormula};

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

    fn parse_expr(&mut self, expr: &'var Expr<T>, coeff: Option<i128>) {
        match expr {
            Expr::Atom(int) => match int {
                Int::Const(_x) => {
                    // if we get here then this is a constraint,
                }
                Int::Var(v) => {
                    // insert var
                    self.vars.insert(v);
                }
            },
            Expr::Add(lhs, rhs) => {
                self.parse_expr(lhs, coeff);
                self.parse_expr(rhs, coeff);
            }
            Expr::Mul(int, rhs) => {
                // here this is something we need to create a constraint for
                // and we need to ensure that there's a coefficient
                self.parse_expr(rhs, None);
            }
        }
    }

    pub fn parse_qflia(&mut self, formula: &'var QFLIAFormula<T>) {
        self.parse_expr(&formula.expr, None);
        todo!()
    }
}
