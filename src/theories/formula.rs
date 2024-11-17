use crate::sat::var::{IntoProp, Lit, SATProp, SATPropOps, Var};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

pub enum BinOp {
    And,
    Or,
    Imp,
    Iff,
}

pub enum UnaryOp {
    Not,
}

pub enum SMTFormula<T> {
    Atom(T),
    UnExpr(Box<SMTFormula<T>>, UnaryOp),
    BinExpr(Box<SMTFormula<T>>, Box<SMTFormula<T>>, BinOp),
}

impl<T> SMTFormula<T> {
    pub fn not(self) -> Self {
        Self::UnExpr(Box::new(self), UnaryOp::Not)
    }

    pub fn and(self, rhs: Self) -> Self {
        Self::BinExpr(Box::new(self), Box::new(rhs), BinOp::And)
    }

    pub fn or(self, rhs: Self) -> Self {
        Self::BinExpr(Box::new(self), Box::new(rhs), BinOp::Or)
    }

    pub fn imp(self, rhs: Self) -> Self {
        Self::BinExpr(Box::new(self), Box::new(rhs), BinOp::Imp)
    }

    pub fn iff(self, rhs: Self) -> Self {
        Self::BinExpr(Box::new(self), Box::new(rhs), BinOp::Iff)
    }
}

pub(crate) struct SMTtoSatPropResolver<'expr, T: Debug + Hash + PartialEq + Eq> {
    curr_stamp: u32,
    formula_to_lit_map: HashMap<&'expr T, Lit<u32>>,
}

impl<'expr, T: Debug + Hash + PartialEq + Eq> SMTtoSatPropResolver<'expr, T> {
    pub fn new() -> Self {
        Self {
            curr_stamp: 0,
            formula_to_lit_map: HashMap::new(),
        }
    }

    fn handle_atom(&mut self, expr: &'expr T) -> SATProp<u32> {
        //
        // Note: Actively going to only push positive lits here.
        // When we do have something like not x, we are going to
        // have the expr not ( pos(x) ) where pos(x) is a positive
        // lit and not is it's negation
        //
        match self.formula_to_lit_map.get(expr) {
            None => {
                // insert curr stamp
                let var = Var::new(self.curr_stamp);
                self.curr_stamp += 1;
                let lit = Lit::pos(var);
                self.formula_to_lit_map.insert(expr, lit);
                lit.into_prop()
            }
            Some(lit) => lit.into_prop(),
        }
    }

    pub fn expr_to_sat_prop(&mut self, expr: &'expr SMTFormula<T>) -> SATProp<u32> {
        match expr {
            SMTFormula::Atom(expr) => self.handle_atom(expr),
            SMTFormula::UnExpr(expr, op) => {
                // negate current lit
                match op {
                    UnaryOp::Not => self.expr_to_sat_prop(expr).not(),
                }
            }
            SMTFormula::BinExpr(lhs, rhs, op) => {
                let new_lhs = self.expr_to_sat_prop(lhs);
                let new_rhs = self.expr_to_sat_prop(rhs);
                match op {
                    BinOp::And => new_lhs.and(new_rhs),
                    BinOp::Or => new_lhs.or(new_rhs),
                    BinOp::Imp => new_lhs.implies(new_rhs),
                    BinOp::Iff => new_lhs.iff(new_rhs),
                }
            }
        }
    }
}
