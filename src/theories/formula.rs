use crate::sat::var::{IntoProp, Lit, Prop, Var};
use crate::theories::qflia::formula::ValidOperand;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use super::qflia::formula::QFLIAFormula;

enum BinOp {
    And,
    Or,
    Imp,
    Iff,
}

enum UnaryOp {
    Not,
}

//
// TODO(VR): Add unary operations like negation to this
//
#[allow(private_interfaces)]
pub enum SMTFormula<T> {
    Atom(T),
    UnExpr(Box<SMTFormula<T>>, UnaryOp),
    BinExpr(Box<SMTFormula<T>>, Box<SMTFormula<T>>, BinOp),
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

    fn handle_atom(&mut self, expr: &'expr T) -> Prop<u32> {
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

    pub fn expr_to_sat_prop(&mut self, expr: &'expr SMTFormula<T>) -> Prop<u32> {
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

pub trait IntoSMT {
    type Inner;

    fn into_smt(self) -> SMTFormula<Self::Inner>;
}

pub trait SMTOps: IntoSMT + Sized {
    fn not(self) -> SMTFormula<Self::Inner> {
        SMTFormula::UnExpr(Box::new(self.into_smt()), UnaryOp::Not)
    }

    fn and<Rhs>(self, rhs: Rhs) -> SMTFormula<Self::Inner>
    where
        Rhs: IntoSMT<Inner = Self::Inner>,
    {
        SMTFormula::BinExpr(
            Box::new(self.into_smt()),
            Box::new(rhs.into_smt()),
            BinOp::And,
        )
    }

    fn or<Rhs>(self, rhs: Rhs) -> SMTFormula<Self::Inner>
    where
        Rhs: IntoSMT<Inner = Self::Inner>,
    {
        SMTFormula::BinExpr(
            Box::new(self.into_smt()),
            Box::new(rhs.into_smt()),
            BinOp::Or,
        )
    }

    fn imp<Rhs>(self, rhs: Rhs) -> SMTFormula<Self::Inner>
    where
        Rhs: IntoSMT<Inner = Self::Inner>,
    {
        SMTFormula::BinExpr(
            Box::new(self.into_smt()),
            Box::new(rhs.into_smt()),
            BinOp::Imp,
        )
    }

    fn iff<Rhs>(self, rhs: Rhs) -> SMTFormula<Self::Inner>
    where
        Rhs: IntoSMT<Inner = Self::Inner>,
    {
        SMTFormula::BinExpr(
            Box::new(self.into_smt()),
            Box::new(rhs.into_smt()),
            BinOp::Iff,
        )
    }
}

impl<T> IntoSMT for SMTFormula<T> {
    type Inner = T;

    fn into_smt(self) -> SMTFormula<Self::Inner> {
        self
    }
}

impl<T: Debug + Hash + PartialEq + Eq> IntoSMT for QFLIAFormula<T> {
    type Inner = QFLIAFormula<T>;

    fn into_smt(self) -> SMTFormula<Self::Inner> {
        // these formulas have to be in bool form
        assert_eq!(self.ensure_bool(), true);
        SMTFormula::Atom(self)
    }
}

//
// impl ops for theories
//
impl<T> SMTOps for SMTFormula<T> {}
impl<T: Debug + Hash + PartialEq + Eq> SMTOps for QFLIAFormula<T> {}
