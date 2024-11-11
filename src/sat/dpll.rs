use std::collections::HashMap;

use super::defs::Formula;

#[derive(Debug, Clone)]
pub struct Solver<'a> {
    formula: Formula<'a>,
}

impl<'a> Solver<'a> {
    pub fn new(formula: Formula<'a>) -> Self {
        Self { formula }
    }

    fn all_assigned(&'a self, assignments: &'a HashMap<&'a str, bool>) -> bool {
        let vars = self
            .formula
            .clauses
            .iter()
            .flat_map(|c| {
                c.vars
                    .iter()
                    .map(|v| v.get_name())
                    .collect::<Vec<&'a str>>()
            })
            .collect::<Vec<&'a str>>();
        for var in vars {
            if assignments.get(var).is_none() {
                return false;
            }
        }
        true
    }

    fn dpll(&mut self, mut assignments: HashMap<&'a str, bool>) -> bool {
        if self.formula.is_satisfied(&assignments) {
            return true;
        } else if self.all_assigned(&assignments) {
            return false;
        }

        // unit prop
        let mut propogated = false;
        for clause in self.formula.clone().clauses {
            if let Some(var) = clause.get_unit_var(&assignments) {
                assignments.insert(var.get_name(), !var.is_negated());
                propogated = true;
            }
        }
        // if we propogated, we should recurse to make sure there are no more unit clauses
        if propogated {
            return self.dpll(assignments);
        }
        // pure literal elimination
        let mut var_map = HashMap::new();
        for clause in self.formula.clone().clauses {
            for var in clause.vars.iter() {
                let name = var.get_name();
                if assignments.get(name).is_none() {
                    let entry = var_map.entry((name, var.is_negated())).or_insert(1);
                    *entry += 1;
                }
            }
        }
        for clause in self.formula.clauses.iter() {
            for var in clause.vars.iter() {
                let name = var.get_name();
                if assignments.get(name).is_none()
                    && !var_map.get(&(name, !var.is_negated())).is_none()
                {
                    assignments.insert(name, !var.is_negated());
                }
            }
        }
        // choose a literal
        for clause in self.formula.clone().clauses {
            for var in clause.vars {
                if assignments.get(var.get_name()).is_none() {
                    // heuristically, it would be absurd to assign something that's negated
                    // to false so we will just do that
                    let mut new_assignments = assignments.clone();
                    new_assignments.insert(var.get_name(), !var.is_negated());
                    assignments.insert(var.get_name(), var.is_negated());
                    return self.clone().dpll(assignments) || self.clone().dpll(new_assignments);
                }
            }
        }

        false
    }

    pub fn run(mut self) -> bool {
        self.dpll(HashMap::new())
    }
}

#[cfg(test)]
mod sat_test {
    use crate::sat::defs::{Clause, Formula, Var};

    use super::Solver;

    #[test]
    fn unsat_simple() {
        let var = Var::new("a");
        let var_neg = Var::negated("a");
        let clause = Clause::new(vec![var]);
        let clause_neg = Clause::new(vec![var_neg]);
        let formula = Formula::new(vec![clause, clause_neg]);
        assert_eq!(Solver::new(formula).run(), false)
    }

    #[test]
    fn sat_single_var() {
        let var = Var::new("a");
        let clause = Clause::new(vec![var]);
        let formula = Formula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_single_var_negated() {
        let var = Var::negated("a");
        let clause = Clause::new(vec![var]);
        let formula = Formula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_complex() {
        // (a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬d) ∧ (c ∨ d ∨ ¬e) ∧ (¬c ∨ ¬d ∨ e) ∧ (b ∨ ¬e ∨ ¬f) ∧ (¬b ∨ f ∨ a)
        let a = Var::new("a");
        let neg_b = Var::negated("b");
        let c = Var::new("c");
        let clause1 = Clause::new(vec![a, neg_b, c]);

        let neg_a = Var::negated("a");
        let b = Var::new("b");
        let neg_d = Var::negated("d");
        let clause2 = Clause::new(vec![neg_a, b, neg_d]);

        let neg_e = Var::negated("e");
        let d = Var::new("d");
        let clause3 = Clause::new(vec![c, d, neg_e]);

        let e = Var::new("e");
        let neg_c = Var::negated("c");
        let clause4 = Clause::new(vec![neg_c, neg_d, e]);

        let neg_f = Var::negated("f");
        let clause5 = Clause::new(vec![b, neg_e, neg_f]);

        let f = Var::new("a");
        let clause6 = Clause::new(vec![neg_b, f, a]);

        let formula = Formula::new(vec![clause1, clause2, clause3, clause4, clause5, clause6]);
        assert_eq!(Solver::new(formula).run(), true);
    }

    #[test]
    fn unsat_complex() {
        // (𝑥∨𝑦∨𝑧) ∧ (𝑥∨𝑦∨¬𝑧) ∧ (𝑥∨¬𝑦∨𝑧) ∧ (𝑥∨¬𝑦∨¬𝑧) ∧ (¬𝑥∨𝑦∨𝑧) ∧ (¬𝑥∨𝑦∨¬𝑧) ∧ (¬𝑥∨¬𝑦∨𝑧) ∧ (¬𝑥∨¬𝑦∨¬𝑧)
        let x = Var::new("x");
        let y = Var::new("y");
        let z = Var::new("z");
        let clause1 = Clause::new(vec![x, y, z]);
        let neg_z = Var::negated("z");
        let clause2 = Clause::new(vec![x, y, neg_z]);
        let neg_y = Var::negated("y");
        let clause3 = Clause::new(vec![x, neg_y, z]);
        let clause4 = Clause::new(vec![x, neg_y, neg_z]);
        let neg_x = Var::negated("x");
        let clause5 = Clause::new(vec![neg_x, y, z]);
        let clause6 = Clause::new(vec![neg_x, y, neg_z]);
        let clause7 = Clause::new(vec![neg_x, neg_y, z]);
        let clause8 = Clause::new(vec![neg_x, neg_y, neg_z]);
        let formula = Formula::new(vec![
            clause1, clause2, clause3, clause4, clause5, clause6, clause7, clause8,
        ]);
        assert_eq!(Solver::new(formula).run(), false);
    }
}
