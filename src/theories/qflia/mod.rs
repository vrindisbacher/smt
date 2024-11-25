use formula::QFLIAFormula;
use simplex::Simplex;

use std::fmt::Debug;
use std::hash::Hash;

pub mod formula;
mod simplex;

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
    goals: Vec<QFLIAFormula<T>>,
}

impl<T: Debug + Hash + PartialEq + Eq> QFLIASolver<T> {
    pub fn new() -> Self {
        Self { goals: Vec::new() }
    }

    pub fn assert(&mut self, goal: QFLIAFormula<T>) {
        // Requires goal to be in bool form
        //
        // Letting this invariant be upheld by the SMT
        // Solver that passes goals to the QFLIA solver
        self.goals.push(goal);
    }

    pub fn solve(&self) -> QFLIASolverResult {
        let mut simplex = Simplex::new();
        for goal in self.goals.iter() {
            simplex.parse_qflia(goal);
        }

        todo!()
    }
}
