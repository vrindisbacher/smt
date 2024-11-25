use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;

use super::simple_formula::{NormExpr, NormQFLIAFormula};

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

    fn parse_expr(&mut self, expr: &'var NormExpr<T>) {
        match expr {
            // TODO: This has to be a variable
            NormExpr::Const(int) => todo!(),
            NormExpr::Var(coeff, int) => todo!(),
            NormExpr::Add(lhs, rhs) => todo!(),
        }
    }

    pub fn parse_qflia(&mut self, formula: &'var NormQFLIAFormula<T>) {
        self.parse_expr(&formula.lhs);
        todo!()
    }
}
