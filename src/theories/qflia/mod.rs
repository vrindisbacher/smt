use formula::{QFLIAFormula, QFLIAUnOp};

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

    fn decompose_goal(&self, goal: &QFLIAFormula<T>) {
        // a goal like: x + y <= 0 should be decompose into a row
        // of a tableau like so:
        //     x y s1 rhs
        // s1  1 1 1  0
        // obj 0 0 0  0
        match goal {
            QFLIAFormula::Atom(x) => match x {},
            QFLIAFormula::UnaryExpr(lhs, op) => match op {
                QFLIAUnOp::Neg => {}
            },
            QFLIAFormula::BinExpr(lhs, rhs, op) => match op {
                formula::QFLIABinOp::Add => todo!(),
                formula::QFLIABinOp::Mul => todo!(),
                formula::QFLIABinOp::Gte => todo!(),
                formula::QFLIABinOp::Lte => todo!(),
            },
        }
    }

    pub fn solve(&self) -> QFLIASolverResult {
        // set up a tableau
        let _tableau: Vec<Vec<i128>> = Vec::new();
        for goal in self.goals.iter() {
            self.decompose_goal(goal)
        }
        todo!()
    }
}
