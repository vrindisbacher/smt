use formula::QFLIAFormula;

use crate::sat::var::Prop;
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
    constraints: Vec<QFLIASolverOperand<T>>,
}

impl<T: Debug + Hash + PartialEq + Eq> QFLIASolver<T> {
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    pub fn add_constraint(&mut self, constraint: QFLIASolverOperand<T>) {
        self.constraints.push(constraint);
    }

    pub fn assert(&mut self, goal: QFLIASolverOperand<T>) -> QFLIASolverResult {
        // turn this into a SAT formula now
        let sat_prop = self.into_sat_prop(&goal);
        if let SATSolverResult::Sat(_assns) = self.find_sat_assignment(sat_prop) {
            todo!()
        } else {
            QFLIASolverResult::Unsat
        }
    }

    fn find_sat_assignment(&self, sat_prop: Prop<u32>) -> SATSolverResult<u32> {
        let solver = crate::sat::SATSolver::new(sat_prop.into_cnf());
        solver.run()
    }

    fn into_sat_prop(&self, goal: &QFLIASolverOperand<T>) -> Prop<u32> {
        let mut smt_to_sat_resolver = SMTtoSatPropResolver::new();
        let mut curr_formula: Prop<u32>;
        // and turn the goal into a prop
        let goal_prop = smt_to_sat_resolver.expr_to_sat_prop(goal);
        // if there are no constraints and just a goal
        // then return that prop on its own
        if self.constraints.len() == 0 {
            return goal_prop;
        }
        // otherwise replace all constraints with Prop's that are joined
        // by conjunction
        curr_formula = smt_to_sat_resolver.expr_to_sat_prop(&self.constraints[0]);
        // skip the first since we've looked at it
        for constraint in self.constraints.iter().skip(1) {
            let prop = smt_to_sat_resolver.expr_to_sat_prop(constraint);
            curr_formula = curr_formula.and(prop);
        }
        // and imply the goal from the constraints
        curr_formula = curr_formula.implies(goal_prop);
        curr_formula
    }
}

#[cfg(test)]
mod qflia_test {
    use crate::theories::formula::SMTOps;

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
        let clause = Int::from_var("a").equals(Int::from_const(0));
        let neg_clause = Int::from_var("a").n_equals(Int::from_const(0));
        let smt_formula = clause.and(neg_clause);
        let mut solver = QFLIASolver::new();
        assert!(solver.assert(smt_formula).is_unsat());
    }
}
