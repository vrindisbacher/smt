mod assignment;
pub mod clause;
pub mod formula;

use std::fmt::Debug;
use std::hash::Hash;
use std::{clone::Clone, collections::HashMap};

use crate::var::{IntoCnf, Lit, Var};
use assignment::Assignments;
use clause::CnfClause;
use formula::CnfFormula;

#[derive(Debug, Clone)]
pub struct Solver<T: PartialEq + Eq + Hash + Debug + Clone> {
    all_vars: Vec<Lit<T>>,
    // lit to vec of clause idxs that contain it
    lit_to_related_clause_map: HashMap<(T, bool), Vec<usize>>,
    // clause idx to lits it's watching
    clause_to_watched_lit_map: HashMap<usize, Vec<usize>>,
    formula: CnfFormula<T>,
}

#[allow(private_bounds)]
impl<T: PartialEq + Eq + Hash + Debug + Clone> Solver<T> {
    pub fn new(formula: impl IntoCnf<T>) -> Self {
        let formula = formula.into_cnf();
        let all_vars = Self::get_all_vars(&formula);
        let clause_to_watched_lit_map = Self::create_clause_to_watched_lit_map(&formula.clauses);
        let lit_to_related_clause_map =
            Self::create_lit_to_related_clause_map(&formula.clauses, &clause_to_watched_lit_map);
        Self {
            all_vars,
            formula,
            clause_to_watched_lit_map,
            lit_to_related_clause_map,
        }
    }

    fn create_clause_to_watched_lit_map(clauses: &Vec<CnfClause<T>>) -> HashMap<usize, Vec<usize>> {
        let mut map = HashMap::new();
        for (idx, clause) in clauses.iter().enumerate() {
            let watchlist;
            if clause.vars.len() >= 2 {
                watchlist = vec![0, 1];
            } else {
                watchlist = vec![0]
            }
            map.insert(idx, watchlist);
        }
        map
    }

    fn create_lit_to_related_clause_map(
        clauses: &Vec<CnfClause<T>>,
        watchlist_map: &HashMap<usize, Vec<usize>>,
    ) -> HashMap<(T, bool), Vec<usize>> {
        let mut map = HashMap::new();
        for (idx, clause) in clauses.iter().enumerate() {
            let watchlist = watchlist_map.get(&idx).expect(
                "Something has gone terribly wrong - clause idx {idx} was not in watchlist map",
            );
            for watch_idx in watchlist.iter() {
                let var = &clause.vars[*watch_idx];
                let var_name = var.get_name().clone();
                let var_negated = var.is_negated();
                map.entry((var_name, var_negated))
                    .and_modify(|e: &mut Vec<usize>| {
                        if !e.contains(&idx) {
                            e.push(idx)
                        }
                    })
                    .or_insert_with(|| vec![idx]);
            }
        }
        map
    }

    fn remove_watching_clause_for_var(&mut self, lit: &Lit<T>, clause_idx: usize) {
        self.lit_to_related_clause_map
            .entry((lit.get_name().clone(), lit.is_negated()))
            .and_modify(|e| {
                if let Some(idx) = e.iter().position(|i| *i == clause_idx) {
                    e.remove(idx);
                }
            });
    }

    fn add_watching_clause_for_var(&mut self, name: T, negated: bool, clause_idx: usize) {
        self.lit_to_related_clause_map
            .entry((name, negated))
            .and_modify(|e| {
                if !e.contains(&clause_idx) {
                    e.push(clause_idx);
                }
            });
    }

    fn resolve_watch(
        &mut self,
        clause_idx: usize,
        lit_to_change: &Lit<T>,
        assignment: &mut Assignments<T>,
    ) -> Result<(), ()> {
        // watchlist is a vec of var idxs in the given clause
        let watchlist = self.clause_to_watched_lit_map.get(&clause_idx).expect(
            "Something has gone terribly wrong - clause idx {idx} was not in watchlist map",
        );
        // let clause = self.formula.clauses[clause_idx].clone();
        let to_change_idxs = watchlist
            .iter()
            .enumerate()
            .find(|(_, idx)| self.formula.clauses[clause_idx].vars[**idx] == *lit_to_change);
        if let Some((to_change_wl_idx, idx_to_change)) = to_change_idxs {
            // now determine is we're looking at 2 vars or 1
            let mut other_idx = None;
            if watchlist.len() == 2 {
                other_idx = Some(watchlist[1 - to_change_wl_idx]);
            }
            let mut new_idx = -1;
            for (idx, var) in self.formula.clauses[clause_idx].vars.iter().enumerate() {
                if idx == *idx_to_change
                    || other_idx.is_some_and(|other_idx: usize| other_idx == idx)
                {
                    continue;
                }
                if let Some(assn) = assignment.get_assignment(var) {
                    log::debug!("Found {var:?} which is assigned true");
                    if assn {
                        log::debug!("It is assigned true");
                        new_idx = idx as i32;
                    }
                } else {
                    log::debug!("Found {var:?} which is unassigned");
                    new_idx = idx as i32;
                }
            }
            if new_idx == -1 {
                if let Some(other_idx) = other_idx {
                    let other_watched = &self.formula.clauses[clause_idx].vars[other_idx];
                    if let Some(assn) = assignment.get_assignment(other_watched) {
                        log::debug!("Other watched idx is assigned");
                        if !assn {
                            return Err(());
                        }
                    }
                    let assn_val = !other_watched.is_negated();
                    assignment.assign(other_watched.get_name().clone(), assn_val);
                } else {
                    return Err(());
                }
            } else {
                // update the vars the clause is looking at
                self.update_clause_watchlist(clause_idx, to_change_wl_idx, new_idx as usize);
                // remove the clause from the lit
                self.remove_watching_clause_for_var(lit_to_change, clause_idx);
                let var = &self.formula.clauses[clause_idx].vars[new_idx as usize];
                let is_negated = var.is_negated();
                let name = var.get_name().clone();
                self.add_watching_clause_for_var(name, is_negated, clause_idx);
            }
            Ok(())
        } else {
            Err(())
        }
    }

    fn clause_watching_true(&self, clause_idx: usize, assignment: &Assignments<T>) -> bool {
        // get the list of idxs for lits in the clause we are looking at
        let watchlist = self.clause_to_watched_lit_map.get(&clause_idx).expect(
            "Something has gone terribly wrong - clause idx {idx} was not in watchlist map",
        );
        for idx in watchlist.iter() {
            if let Some(assn) =
                assignment.get_assignment(&self.formula.clauses[clause_idx].vars[*idx])
            {
                if assn {
                    return true;
                }
            }
        }
        false
    }

    fn get_watching_clauses_for_var(&self, lit: &Lit<T>) -> Option<Vec<usize>> {
        Some(
            self.lit_to_related_clause_map
                .get(&(lit.get_name().clone(), lit.is_negated()))?
                .clone(),
        )
    }

    fn update_clause_watchlist(
        &mut self,
        clause_idx: usize,
        to_change_wl_idx: usize,
        new_idx: usize,
    ) {
        log::debug!(
            "Updating watchlist for {:?} from {:?}",
            self.formula.clauses[clause_idx],
            self.clause_to_watched_lit_map.get(&clause_idx)
        );
        self.clause_to_watched_lit_map
            .entry(clause_idx)
            // set the new wl lit being watched to new idx
            .and_modify(|w| {
                log::debug!("Making modification to wl {w:?}");
                w[to_change_wl_idx] = new_idx
            });
        log::debug!(
            "Updated watchlist for {:?} to {:?}",
            self.formula.clauses[clause_idx],
            self.clause_to_watched_lit_map.get(&clause_idx)
        );
    }

    fn get_all_vars(formula: &CnfFormula<T>) -> Vec<Lit<T>> {
        let mut vars = vec![];
        for clause in formula.clauses.iter() {
            for var in clause.vars.iter() {
                if !vars.contains(var) {
                    vars.push(var.clone())
                }
            }
        }
        vars
    }

    fn all_assigned(&self, assignments: &Assignments<T>) -> bool {
        for var in self.all_vars.iter() {
            if assignments.get_assignment(&var).is_none() {
                return false;
            }
        }
        true
    }

    fn get_next_to_assign(&self, assignments: &Assignments<T>) -> Option<&Var<T>> {
        for var in self.all_vars.iter() {
            if assignments.get_assignment(&var).is_none() {
                return Some(var.get_var());
            }
        }
        None
    }

    fn unit_prop(&mut self, assignments: &mut Assignments<T>) -> Result<(), ()> {
        while assignments.propogation_queue.len() > 0 {
            // var has the negation of a freshly assigned variable
            // SAFETY: len is > 0
            let var = assignments.propogation_queue.pop_front().unwrap();
            log::debug!("Looking at {var:?} in propogation queue");
            // Get all clauses that relate to the clause
            // If the negated assignment causes a conflict, we need to
            // resolve
            let clause_idxs = match self.get_watching_clauses_for_var(&var) {
                None => continue,
                Some(idxs) => idxs,
            };
            for clause_idx in clause_idxs {
                log::debug!(
                    "Looking at watching clause {:?}",
                    self.formula.clauses[clause_idx]
                );
                if let Some(assn) = assignments.get_assignment(&var) {
                    // we have a valid assignment for the current variable so we're good
                    if assn {
                        log::debug!("Valid assignment for var {var:?}. Continuing.");
                        continue;
                    }
                } else {
                    // can't cause a conflict because it's unassigned
                    log::debug!("Found an unassigned variable in clause. Continuing");
                    continue;
                }

                if self.clause_watching_true(clause_idx, assignments) {
                    log::debug!("Found at least one true var in clause. continuing");
                    // this assignment isn't valid but we are watching something with a valid
                    // assignment
                    continue;
                }

                log::debug!(
                    "Resolving watched lits for clause. Here is the clauses watchlist {:?}",
                    self.clause_to_watched_lit_map.get(&clause_idx).unwrap()
                );
                self.resolve_watch(clause_idx, &var, assignments)?;
                log::debug!(
                    "Successfully resolved watchlist. Here is the clauses new watchlist {:?}",
                    self.clause_to_watched_lit_map.get(&clause_idx).unwrap()
                );
            }
        }
        log::debug!("Successfully completed unit propogation");
        Ok(())
    }

    fn dpll(&mut self, assignments: &mut Assignments<T>) -> bool {
        while !self.all_assigned(assignments) {
            log::debug!("In DPLL Loop with some unassigned");
            if self.unit_prop(assignments).is_err() {
                log::debug!("Unit Propogation returned an error. Failing.");
                return false;
            }
            // SAFETY: Check that all aren't assigned at the beginning
            let to_assign = self.get_next_to_assign(assignments).unwrap();
            assignments.create_decision_level(to_assign, true);
            log::debug!(
                "Created new decision level with {:?} assigned true",
                to_assign.get_name()
            );

            while self.unit_prop(assignments).is_err() {
                if assignments.assignments_stack.len() <= 1 {
                    return false;
                }
                // SAFETY: We just checked that there's at least one element
                let (conflicting_var, conflict_assn) = assignments.backtrack();
                log::debug!(
                    "Conflicting var {:?} found. It was assigned {}",
                    conflicting_var.get_name(),
                    conflict_assn
                );
                let flipped_assn = !conflict_assn;
                assignments.assign(conflicting_var.get_name().clone(), flipped_assn);
                log::debug!(
                    "Assigned var {:?} {}",
                    conflicting_var.get_name(),
                    flipped_assn
                );
            }
        }
        true
    }

    pub fn run(mut self) -> bool {
        let mut assignments = Assignments::new();
        self.dpll(&mut assignments)
    }
}

#[cfg(test)]
mod sat_test {
    use crate::dimacs::parse_formula_from_dimacs_str;
    use crate::sat::{clause::CnfClause, formula::CnfFormula};
    use crate::var::{Lit, Var};

    use super::Solver;

    #[test]
    fn unsat_simple() {
        let var_a = Var::new("a");
        let var = Lit::pos(var_a);
        let var_neg = Lit::neg(var_a);
        let clause = CnfClause::new(vec![var]);
        let clause_neg = CnfClause::new(vec![var_neg]);
        let formula = CnfFormula::new(vec![clause, clause_neg]);
        assert_eq!(Solver::new(formula).run(), false)
    }

    #[test]
    fn sat_single_var() {
        let var_a = Var::new("a");
        let var = Lit::pos(var_a);
        let clause = CnfClause::new(vec![var]);
        let formula = CnfFormula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_single_var_negated() {
        let var_a = Var::new("a");
        let var = Lit::neg(var_a);
        let clause = CnfClause::new(vec![var]);
        let formula = CnfFormula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_neg_unit_prop() {
        let var_a = Var::new("a");
        let var1 = Lit::pos(var_a);
        let var1_neg = Lit::neg(var_a);
        let var_b = Var::new("b");
        let var2 = Lit::pos(var_b);
        let clause1 = CnfClause::new(vec![var1_neg]);
        let clause2 = CnfClause::new(vec![var1, var2]);
        let formula = CnfFormula::new(vec![clause1, clause2]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_complex() {
        // (a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬d) ∧ (c ∨ d ∨ ¬e) ∧ (¬c ∨ ¬d ∨ e) ∧ (b ∨ ¬e ∨ ¬f) ∧ (¬b ∨ f ∨ a)
        let var_a = Var::new("a");
        let var_b = Var::new("b");
        let var_c = Var::new("c");
        let var_d = Var::new("d");
        let var_e = Var::new("e");
        let var_f = Var::new("f");

        let a = Lit::pos(var_a);
        let neg_b = Lit::neg(var_b);
        let c = Lit::pos(var_c);
        let clause1 = CnfClause::new(vec![a, neg_b, c]);

        let neg_a = Lit::neg(var_a);
        let b = Lit::pos(var_b);
        let neg_d = Lit::neg(var_d);
        let clause2 = CnfClause::new(vec![neg_a, b, neg_d]);

        let neg_e = Lit::neg(var_e);
        let d = Lit::pos(var_d);
        let clause3 = CnfClause::new(vec![c, d, neg_e]);

        let e = Lit::pos(var_e);
        let neg_c = Lit::neg(var_c);
        let clause4 = CnfClause::new(vec![neg_c, neg_d, e]);

        let neg_f = Lit::neg(var_f);
        let clause5 = CnfClause::new(vec![b, neg_e, neg_f]);

        let f = Lit::pos(var_a);
        let clause6 = CnfClause::new(vec![neg_b, f, a]);

        let formula = CnfFormula::new(vec![clause1, clause2, clause3, clause4, clause5, clause6]);
        assert_eq!(Solver::new(formula).run(), true);
    }

    #[test]
    fn unsat_complex() {
        // (𝑥∨𝑦∨𝑧) ∧ (𝑥∨𝑦∨¬𝑧) ∧ (𝑥∨¬𝑦∨𝑧) ∧ (𝑥∨¬𝑦∨¬𝑧) ∧ (¬𝑥∨𝑦∨𝑧) ∧ (¬𝑥∨𝑦∨¬𝑧) ∧ (¬𝑥∨¬𝑦∨𝑧) ∧ (¬𝑥∨¬𝑦∨¬𝑧)
        let var_x = Var::new("x");
        let var_y = Var::new("z");
        let var_z = Var::new("z");
        let x = Lit::pos(var_x);
        let y = Lit::pos(var_y);
        let z = Lit::pos(var_z);
        let clause1 = CnfClause::new(vec![x, y, z]);
        let neg_z = Lit::neg(var_z);
        let clause2 = CnfClause::new(vec![x, y, neg_z]);
        let neg_y = Lit::neg(var_y);
        let clause3 = CnfClause::new(vec![x, neg_y, z]);
        let clause4 = CnfClause::new(vec![x, neg_y, neg_z]);
        let neg_x = Lit::neg(var_x);
        let clause5 = CnfClause::new(vec![neg_x, y, z]);
        let clause6 = CnfClause::new(vec![neg_x, y, neg_z]);
        let clause7 = CnfClause::new(vec![neg_x, neg_y, z]);
        let clause8 = CnfClause::new(vec![neg_x, neg_y, neg_z]);
        let formula = CnfFormula::new(vec![
            clause1, clause2, clause3, clause4, clause5, clause6, clause7, clause8,
        ]);
        assert_eq!(Solver::new(formula).run(), false);
    }

    #[test]
    fn simple_dimacs() {
        let str = "
          c  simple_v3_c2.cnf
          c  satisfiable
          c
          p cnf 3 2
          1 -3 0
          2 3 -1 0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), true);
    }
    #[test]
    fn simple_dimacs2() {
        let str = "
            p cnf 5 3
            1 -5 4 0
            -1 5 3 4 0
            -3 -4 0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), true);
    }

    #[test]
    fn aim_100_1_6_no() {
        let str = "
            c FILE: aim-100-1_6-no-1.cnf
            c
            c SOURCE: Kazuo Iwama, Eiji Miyano (miyano@cscu.kyushu-u.ac.jp),
            c          and Yuichi Asahiro
            c
            c DESCRIPTION: Artifical instances from generator by source.  Generators
            c              and more information in sat/contributed/iwama.
            c
            c NOTE: Not Satisfiable
            c
            p cnf 100 160
            16 30 95 0
            -16 30 95 0
            -30 35 78 0
            -30 -78 85 0
            -78 -85 95 0
            8 55 100 0
            8 55 -95 0
            9 52 100 0
            9 73 -100 0
            -8 -9 52 0
            38 66 83 0
            -38 83 87 0
            -52 83 -87 0
            66 74 -83 0
            -52 -66 89 0
            -52 73 -89 0
            -52 73 -74 0
            -8 -73 -95 0
            40 -55 90 0
            -40 -55 90 0
            25 35 82 0
            -25 82 -90 0
            -55 -82 -90 0
            11 75 84 0
            11 -75 96 0
            23 -75 -96 0
            -11 23 -35 0
            -23 29 65 0
            29 -35 -65 0
            -23 -29 84 0
            -35 54 70 0
            -54 70 77 0
            19 -77 -84 0
            -19 -54 70 0
            22 68 81 0
            -22 48 81 0
            -22 -48 93 0
            3 -48 -93 0
            7 18 -81 0
            -7 56 -81 0
            3 18 -56 0
            -18 47 68 0
            -18 -47 -81 0
            -3 68 77 0
            -3 -77 -84 0
            19 -68 -70 0
            -19 -68 74 0
            -68 -70 -74 0
            54 61 -62 0
            50 53 -62 0
            -50 61 -62 0
            -27 56 93 0
            4 14 76 0
            4 -76 96 0
            -4 14 80 0
            -14 -68 80 0
            -10 -39 -89 0
            1 49 -81 0
            1 26 -49 0
            17 -26 -49 0
            -1 17 -40 0
            16 51 -89 0
            -9 57 60 0
            12 45 -51 0
            2 12 69 0
            2 -12 40 0
            -12 -51 69 0
            -33 60 -98 0
            5 -32 -66 0
            2 -47 -100 0
            -42 64 83 0
            20 -42 -64 0
            20 -48 98 0
            -20 50 98 0
            -32 -50 98 0
            -24 37 -73 0
            -24 -37 -100 0
            -57 71 81 0
            -37 40 -91 0
            31 42 81 0
            -31 42 72 0
            -31 42 -72 0
            7 -19 25 0
            -1 -25 -94 0
            -15 -44 79 0
            -6 31 46 0
            -39 41 88 0
            28 -39 43 0
            28 -43 -88 0
            -4 -28 -88 0
            -30 -39 -41 0
            -29 33 88 0
            -16 21 94 0
            -10 26 62 0
            -11 -64 86 0
            -6 -41 76 0
            38 -46 93 0
            26 -37 94 0
            -26 53 -79 0
            78 87 -94 0
            65 76 -87 0
            23 51 -62 0
            -11 -36 57 0
            41 59 -65 0
            -56 72 -91 0
            13 -20 -46 0
            -13 15 79 0
            -17 47 -60 0
            -13 -44 99 0
            -7 -38 67 0
            37 -49 62 0
            -14 -17 -79 0
            -13 -15 -22 0
            32 -33 -34 0
            24 45 48 0
            21 24 -48 0
            -36 64 -85 0
            10 -61 67 0
            -5 44 59 0
            -80 -85 -99 0
            6 37 -97 0
            -21 -34 64 0
            -5 44 46 0
            58 -76 97 0
            -21 -36 75 0
            -15 58 -59 0
            -58 -76 -99 0
            -2 15 33 0
            -26 34 -57 0
            -18 -82 -92 0
            27 -80 -97 0
            6 32 63 0
            -34 -86 92 0
            13 -61 97 0
            -28 43 -98 0
            5 39 -86 0
            39 -45 92 0
            27 -43 97 0
            13 -58 -86 0
            -28 -67 -93 0
            -69 85 99 0
            42 71 -72 0
            10 -27 -63 0
            -59 63 -83 0
            36 86 -96 0
            -2 36 75 0
            -59 -71 89 0
            36 -67 91 0
            36 -60 63 0
            -63 91 -93 0
            25 87 92 0
            -21 49 -71 0
            -2 10 22 0
            6 -18 41 0
            6 71 -92 0
            -53 -69 -71 0
            -2 -53 -58 0
            43 -45 -96 0
            34 -45 -69 0
            63 -86 -98 0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), false);
    }

    #[test]
    fn aim_50_1_6_yes() {
        let str = "
            c FILE: aim-50-1_6-yes1-4.cnf
            c
            c SOURCE: Kazuo Iwama, Eiji Miyano (miyano@cscu.kyushu-u.ac.jp),
            c          and Yuichi Asahiro
            c
            c DESCRIPTION: Artifical instances from generator by source.  Generators
            c              and more information in sat/contributed/iwama.
            c
            c NOTE: Satisfiable
            c
            p cnf 50 80
            16 17 30 0
            -17 22 30 0
            -17 -22 30 0
            16 -30 47 0
            16 -30 -47 0
            -16 -21 31 0
            -16 -21 -31 0
            -16 21 -28 0
            -13 21 28 0
            13 -16 18 0
            13 -18 -38 0
            13 -18 -31 0
            31 38 44 0
            -8 31 -44 0
            8 -12 -44 0
            8 12 -27 0
            12 27 40 0
            -4 27 -40 0
            12 23 -40 0
            -3 4 -23 0
            3 -23 -49 0
            3 -13 -49 0
            -23 -26 49 0
            12 -34 49 0
            -12 26 -34 0
            19 34 36 0
            -19 26 36 0
            -30 34 -36 0
            24 34 -36 0
            -24 -36 43 0
            6 42 -43 0
            -24 42 -43 0
            -5 -24 -42 0
            5 20 -42 0
            5 -7 -20 0
            4 7 10 0
            -4 10 -20 0
            7 -10 -41 0
            -10 41 46 0
            -33 41 -46 0
            33 -37 -46 0
            32 33 37 0
            6 -32 37 0
            -6 25 -32 0
            -6 -25 -48 0
            -9 28 48 0
            -9 -25 -28 0
            19 -25 48 0
            2 9 -19 0
            -2 -19 35 0
            -2 22 -35 0
            -22 -35 50 0
            -17 -35 -50 0
            -29 -35 -50 0
            -1 29 -50 0
            1 11 29 0
            -11 17 -45 0
            -11 39 45 0
            -26 39 45 0
            -3 -26 45 0
            -11 15 -39 0
            14 -15 -39 0
            14 -15 -45 0
            14 -15 -27 0
            -14 -15 47 0
            17 17 40 0
            1 -29 -31 0
            -7 32 38 0
            -14 -33 -47 0
            -1 2 -8 0
            35 43 44 0
            21 21 24 0
            20 29 -48 0
            23 35 -37 0
            2 18 -33 0
            15 25 -45 0
            9 14 -38 0
            -5 11 50 0
            -3 -13 46 0
            -13 -41 43 0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn dubois_20() {
        let str = "
            c FILE: dubois20.cnf
            c
            c SOURCE: Olivier Dubois (dubois@laforia.ibp.fr)
            c
            c DESCRIPTION: Instance from generator gensathard.c
            c
            c NOTE: Not satisfiable
            c
            c d = 20
            c n = 60
            c p = 160
            c r = 3
            p cnf 60 160
             39  40   1  0
            -39 -40   1  0
             39 -40  -1  0
            -39  40  -1  0
              1  41   2  0
             -1 -41   2  0
              1 -41  -2  0
             -1  41  -2  0
              2  42   3  0
             -2 -42   3  0
              2 -42  -3  0
             -2  42  -3  0
              3  43   4  0
             -3 -43   4  0
              3 -43  -4  0
             -3  43  -4  0
              4  44   5  0
             -4 -44   5  0
              4 -44  -5  0
             -4  44  -5  0
              5  45   6  0
             -5 -45   6  0
              5 -45  -6  0
             -5  45  -6  0
              6  46   7  0
             -6 -46   7  0
              6 -46  -7  0
             -6  46  -7  0
              7  47   8  0
             -7 -47   8  0
              7 -47  -8  0
             -7  47  -8  0
              8  48   9  0
             -8 -48   9  0
              8 -48  -9  0
             -8  48  -9  0
              9  49  10  0
             -9 -49  10  0
              9 -49 -10  0
             -9  49 -10  0
             10  50  11  0
            -10 -50  11  0
             10 -50 -11  0
            -10  50 -11  0
             11  51  12  0
            -11 -51  12  0
             11 -51 -12  0
            -11  51 -12  0
             12  52  13  0
            -12 -52  13  0
             12 -52 -13  0
            -12  52 -13  0
             13  53  14  0
            -13 -53  14  0
             13 -53 -14  0
            -13  53 -14  0
             14  54  15  0
            -14 -54  15  0
             14 -54 -15  0
            -14  54 -15  0
             15  55  16  0
            -15 -55  16  0
             15 -55 -16  0
            -15  55 -16  0
             16  56  17  0
            -16 -56  17  0
             16 -56 -17  0
            -16  56 -17  0
             17  57  18  0
            -17 -57  18  0
             17 -57 -18  0
            -17  57 -18  0
             18  58  19  0
            -18 -58  19  0
             18 -58 -19  0
            -18  58 -19  0
             19  59  60  0
            -19 -59  60  0
             19 -59 -60  0
            -19  59 -60  0
             20  59  60  0
            -20 -59  60  0
             20 -59 -60  0
            -20  59 -60  0
             21  58  20  0
            -21 -58  20  0
             21 -58 -20  0
            -21  58 -20  0
             22  57  21  0
            -22 -57  21  0
             22 -57 -21  0
            -22  57 -21  0
             23  56  22  0
            -23 -56  22  0
             23 -56 -22  0
            -23  56 -22  0
             24  55  23  0
            -24 -55  23  0
             24 -55 -23  0
            -24  55 -23  0
             25  54  24  0
            -25 -54  24  0
             25 -54 -24  0
            -25  54 -24  0
             26  53  25  0
            -26 -53  25  0
             26 -53 -25  0
            -26  53 -25  0
             27  52  26  0
            -27 -52  26  0
             27 -52 -26  0
            -27  52 -26  0
             28  51  27  0
            -28 -51  27  0
             28 -51 -27  0
            -28  51 -27  0
             29  50  28  0
            -29 -50  28  0
             29 -50 -28  0
            -29  50 -28  0
             30  49  29  0
            -30 -49  29  0
             30 -49 -29  0
            -30  49 -29  0
             31  48  30  0
            -31 -48  30  0
             31 -48 -30  0
            -31  48 -30  0
             32  47  31  0
            -32 -47  31  0
             32 -47 -31  0
            -32  47 -31  0
             33  46  32  0
            -33 -46  32  0
             33 -46 -32  0
            -33  46 -32  0
             34  45  33  0
            -34 -45  33  0
             34 -45 -33  0
            -34  45 -33  0
             35  44  34  0
            -35 -44  34  0
             35 -44 -34  0
            -35  44 -34  0
             36  43  35  0
            -36 -43  35  0
             36 -43 -35  0
            -36  43 -35  0
             37  42  36  0
            -37 -42  36  0
             37 -42 -36  0
            -37  42 -36  0
             38  41  37  0
            -38 -41  37  0
             38 -41 -37  0
            -38  41 -37  0
             39  40 -38  0
            -39 -40 -38  0
             39 -40  38  0
            -39  40  38  0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), false);
    }

    #[test]
    fn par8() {
        let str = "
            c FILE:  par8-1-c.cnf
            c
            c SOURCE: James Crawford (jc@research.att.com)
            c
            c DESCRIPTION: Instance arises from the problem of learning the parity
            c              function.  
            c
            c     parxx-y denotes a parity problem on xx bits.  y is simply the
            c     intance number.
            c
            c     parxx-y-c denotes an instance identical to parxx-y except that
            c     the instances have been simplified (to create an equivalent
            c     problem). 
            c
            c NOTE: Satisfiable (checked for 8 and 16 size instances. All
            c       instances are satisfiable by construction)
            c
            c NOTE: Number of clauses corrected August 3, 1993
            c
            c Converted from tableau format Tue Aug  3 09:55:20 EDT 1993
            p cnf 64 254
             -2 1
             0
             -3 -2
             0
             -3 -2 -1
             0
             3 2 -1
             0
             -3 2 1
             0
             3 -2 1
             0
             -4 2
             0
             -5 -4
             0
             -5 -4 -2
             0
             5 4 -2
             0
             -5 4 2
             0
             5 -4 2
             0
             -6 4
             0
             -7 -6
             0
             -7 -6 -4
             0
             7 6 -4
             0
             -7 6 4
             0
             7 -6 4
             0
             -8 6
             0
             -9 -8
             0
             -9 -8 -6
             0
             9 8 -6
             0
             -9 8 6
             0
             9 -8 6
             0
             -10 8
             0
             -11 -10
             0
             -11 -10 -8
             0
             11 10 -8
             0
             -11 10 8
             0
             11 -10 8
             0
             -12 10
             0
             -13 -12
             0
             -13 -12 -10
             0
             13 12 -10
             0
             -13 12 10
             0
             13 -12 10
             0
             -14 12
             0
             -15 -14
             0
             -15 -14 -12
             0
             15 14 -12
             0
             -15 14 12
             0
             15 -14 12
             0
             -16 14
             0
             -17 -16
             0
             -17 -16 -14
             0
             17 16 -14
             0
             -17 16 14
             0
             17 -16 14
             0
             -18 16
             0
             -19 -18
             0
             -19 -18 -16
             0
             19 18 -16
             0
             -19 18 16
             0
             19 -18 16
             0
             -20 18
             0
             -21 -20
             0
             -21 -20 -18
             0
             21 20 -18
             0
             -21 20 18
             0
             21 -20 18
             0
             -22 20
             0
             -23 -22
             0
             -23 -22 -20
             0
             23 22 -20
             0
             -23 22 20
             0
             23 -22 20
             0
             -24 22
             0
             -25 -24
             0
             -25 -24 -22
             0
             25 24 -22
             0
             -25 24 22
             0
             25 -24 22
             0
             -26 24
             0
             -27 -26
             0
             -27 -26 -24
             0
             27 26 -24
             0
             -27 26 24
             0
             27 -26 24
             0
             -28 26
             0
             -29 -28
             0
             -29 -28 -26
             0
             29 28 -26
             0
             -29 28 26
             0
             29 -28 26
             0
             28 -30
             0
             -31 -30
             0
             -31 -28 -30
             0
             31 -28 30
             0
             -31 28 30
             0
             31 28 -30
             0
             -33 -32 -3
             0
             33 32 -3
             0
             -33 32 3
             0
             33 -32 3
             0
             -35 -34 -32
             0
             35 34 -32
             0
             -35 34 32
             0
             35 -34 32
             0
             -37 -34 36
             0
             37 -34 -36
             0
             -37 34 -36
             0
             37 34 36
             0
             -39 -38 -5
             0
             39 38 -5
             0
             -39 38 5
             0
             39 -38 5
             0
             -35 -40 -38
             0
             35 40 -38
             0
             -35 40 38
             0
             35 -40 38
             0
             -42 -41 -40
             0
             42 41 -40
             0
             -42 41 40
             0
             42 -41 40
             0
             -36 -41 43
             0
             36 -41 -43
             0
             -36 41 -43
             0
             36 41 43
             0
             -44 -7 29
             0
             44 -7 -29
             0
             44 7 29
             0
             -44 7 -29
             0
             -33 -45 -44
             0
             33 45 -44
             0
             -33 45 44
             0
             33 -45 44
             0
             -37 -36 -45
             0
             37 36 -45
             0
             -37 36 45
             0
             37 -36 45
             0
             -37 -46 -9
             0
             37 46 -9
             0
             -37 46 9
             0
             37 -46 9
             0
             -36 -43 -46
             0
             36 43 -46
             0
             -36 43 46
             0
             36 -43 46
             0
             -39 -47 -11
             0
             39 47 -11
             0
             -39 47 11
             0
             39 -47 11
             0
             -33 -48 -47
             0
             33 48 -47
             0
             -33 48 47
             0
             33 -48 47
             0
             -37 -36 -48
             0
             37 36 -48
             0
             -37 36 48
             0
             37 -36 48
             0
             -39 -49 -13
             0
             39 49 -13
             0
             -39 49 13
             0
             39 -49 13
             0
             -33 -36 -49
             0
             33 36 -49
             0
             -33 36 49
             0
             33 -36 49
             0
             -50 -15 29
             0
             50 -15 -29
             0
             50 15 29
             0
             -50 15 -29
             0
             -35 -37 -50
             0
             35 37 -50
             0
             -35 37 50
             0
             35 -37 50
             0
             -39 -35 -17
             0
             39 35 -17
             0
             -39 35 17
             0
             39 -35 17
             0
             -39 -51 -19
             0
             39 51 -19
             0
             -39 51 19
             0
             39 -51 19
             0
             -35 -52 -51
             0
             35 52 -51
             0
             -35 52 51
             0
             35 -52 51
             0
             -37 -52 42
             0
             37 -52 -42
             0
             -37 52 -42
             0
             37 52 42
             0
             -53 -21 29
             0
             53 -21 -29
             0
             53 21 29
             0
             -53 21 -29
             0
             -33 -54 -53
             0
             33 54 -53
             0
             -33 54 53
             0
             33 -54 53
             0
             -35 -54 42
             0
             35 -54 -42
             0
             -35 54 -42
             0
             35 54 42
             0
             -33 -23 42
             0
             33 -23 -42
             0
             -33 23 -42
             0
             33 23 42
             0
             -55 -25 29
             0
             55 -25 -29
             0
             55 25 29
             0
             -55 25 -29
             0
             -33 -56 -55
             0
             33 56 -55
             0
             -33 56 55
             0
             33 -56 55
             0
             -35 -56 36
             0
             35 -56 -36
             0
             -35 56 -36
             0
             35 56 36
             0
             -39 -57 -27
             0
             39 57 -27
             0
             -39 57 27
             0
             39 -57 27
             0
             -58 -57 29
             0
             58 -57 -29
             0
             58 57 29
             0
             -58 57 -29
             0
             -35 -59 -58
             0
             35 59 -58
             0
             -35 59 58
             0
             35 -59 58
             0
             -37 -59 -36
             0
             37 -59 36
             0
             -37 59 36
             0
             37 59 -36
             0
             -37 -60 -31
             0
             37 60 -31
             0
             -37 60 31
             0
             37 -60 31
             0
             -42 -61 -60
             0
             42 61 -60
             0
             -42 61 60
             0
             42 -61 60
             0
             -36 -61 43
             0
             36 -61 -43
             0
             -36 61 -43
             0
             36 61 43
             0
             -39 -62 -30
             0
             39 62 -30
             0
             -39 62 30
             0
             39 -62 30
             0
             -33 -63 -62
             0
             33 63 -62
             0
             -33 63 62
             0
             33 -63 62
             0
             -42 -64 -63
             0
             42 64 -63
             0
             -42 64 63
             0
             42 -64 63
             0
             -36 -64 -43
             0
             36 -64 43
             0
             -36 64 43
             0
             36 64 -43
             0
        ";
        let formula = parse_formula_from_dimacs_str(str);
        assert_eq!(Solver::new(formula).run(), true);
    }

    #[test]
    fn obviously_unsat_iff() {
        let var_x = Var::new("x");
        let x = Lit::pos(var_x);
        let neg_x = Lit::neg(var_x);
        let formula = x.iff(neg_x);
        assert_eq!(Solver::new(formula.into_cnf()).run(), false);
    }

    #[test]
    fn obviously_sat_iff() {
        let var_x = Var::new("x");
        let x = Lit::pos(var_x);
        let formula = x.iff(x);
        assert_eq!(Solver::new(formula.into_cnf()).run(), true);
    }

    #[test]
    fn obviously_sat_imp() {
        let var_x = Var::new("x");
        let var_y = Var::new("y");
        let x = Lit::pos(var_x);
        let y = Lit::pos(var_y);
        let formula = x.implies(y);
        assert_eq!(Solver::new(formula.into_cnf()).run(), true);
    }

    #[test]
    fn tricky_sat_imp() {
        let var_x = Var::new("x");
        let x = Lit::pos(var_x);
        let neg_x = Lit::neg(var_x);
        let formula = neg_x.implies(x);
        assert_eq!(Solver::new(formula.into_cnf()).run(), true);
    }

    #[test]
    fn sat_arbitrary_to_cnf() {
        let var_x = Var::new("x");
        let var_y = Var::new("y");
        let var_z = Var::new("z");
        let var_w = Var::new("w");

        let x = Lit::pos(var_x);
        let y = Lit::pos(var_y);
        let not_z = Lit::neg(var_z);
        let w = Lit::pos(var_w);

        let formula = ((x.or(y)).and(not_z)).implies(w);
        assert_eq!(Solver::new(formula.into_cnf()).run(), true);
    }
}
