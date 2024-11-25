use formula::QFLIAFormula;

use crate::sat::var::{SATProp, SATPropOps};
use crate::sat::SATSolverResult;
use crate::theories::formula::SMTtoSatPropResolver;

use super::formula::SMTFormula;
use std::fmt::Debug;
use std::hash::Hash;

pub mod formula;

type QFLIASolverOperand<T> = SMTFormula<QFLIAFormula<T>>;

pub enum QFLIASolverResult {
    Sat,
    Unsat,
}

impl QFLIASolverResult {
    pub fn is_sat(&self) -> bool {
        match self {
            QFLIASolverResult::Sat => true,
            QFLIASolverResult::Unsat => false,
        }
    }

    pub fn is_unsat(&self) -> bool {
        !self.is_sat()
    }
}

pub struct QFLIASolver<T: Debug + Hash + PartialEq + Eq> {
    // QFLIA solver has constraints which are QFLIA Formulas
    // possibly joined by conjunctions or disjunctions or other crazy stuff
    goals: Vec<QFLIASolverOperand<T>>,
}

impl<T: Debug + Hash + PartialEq + Eq> QFLIASolver<T> {
    pub fn new() -> Self {
        Self { goals: Vec::new() }
    }

    pub fn assert(&mut self, goal: QFLIASolverOperand<T>) {
        self.goals.push(goal);
    }

    pub fn solve(&self) -> QFLIASolverResult {
        todo!()
    }
}

#[cfg(test)]
mod qflia_test {

    use super::{
        formula::{Int, QFLIAOp},
        QFLIASolver,
    };

    #[test]
    pub fn unsat_from_sat_assignment() {
        // analogous to a /\ not a
        //
        // this is a good test because it requires that
        // the formula is normalized properly
        // i.e. not a != 0 is transformed into not (a = 0)
        // so that the sat formula we get is actually a /\ not a
        let clause = Int::from_var("a").eq(Int::from_const(0));
        let neg_clause = Int::from_var("a").neq(Int::from_const(0));
        let smt_formula = clause.and(neg_clause);
        let mut solver = QFLIASolver::new();
        assert!(solver.assert(smt_formula).is_unsat());
    }
}
