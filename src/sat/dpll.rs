use std::clone::Clone;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use super::defs::{Clause, Formula, Lit};

#[derive(Debug, Clone)]
pub struct Solver<T: PartialEq + Eq + Hash + Debug + Clone> {
    formula: Formula<T>,
    all_vars: Vec<T>,
    pure_literals: Vec<Lit<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Solver<T> {
    pub fn new(formula: Formula<T>) -> Self {
        let all_vars = Self::get_all_vars(&formula);
        let pure_literals = Self::compute_pure_literals(&formula);
        Self {
            formula,
            all_vars,
            pure_literals,
        }
    }

    fn get_all_vars(formula: &Formula<T>) -> Vec<T> {
        let mut vars = vec![];
        for clause in formula.clauses.iter() {
            for var in clause.vars.iter() {
                if !vars.contains(var.get_name()) {
                    vars.push(var.get_name().clone())
                }
            }
        }
        vars
    }

    fn all_assigned(&self, assignments: &HashMap<T, bool>) -> bool {
        for var in self.all_vars.iter() {
            if assignments.get(var).is_none() {
                return false;
            }
        }
        true
    }

    fn unit_prop<'a>(
        &'a self,
        assignments: &'a mut HashMap<T, bool>,
        satisfied_clauses: &mut Vec<Clause<T>>,
    ) {
        // unit prop
        loop {
            let mut propogated = false;
            for clause in self.formula.clauses.iter() {
                if satisfied_clauses.contains(clause) {
                    continue;
                }
                if clause.is_satisfied(assignments) {
                    satisfied_clauses.push(clause.clone());
                    continue;
                }
                if let Some(var) = clause.get_unit_var(&assignments) {
                    assignments.insert(var.get_name().clone(), !var.is_negated());
                    propogated = true;
                    satisfied_clauses.push(clause.clone());
                }
            }
            // all unit props are gone
            if !propogated {
                break;
            }
        }
    }

    fn compute_pure_literals(formula: &Formula<T>) -> Vec<Lit<T>> {
        let mut var_map = HashMap::new();
        for clause in formula.clauses.iter() {
            for var in clause.vars.iter() {
                let name = var.get_name();
                let entry = var_map.entry((name, var.is_negated())).or_insert(1);
                *entry += 1;
            }
        }

        let mut pures = vec![];
        for clause in formula.clauses.iter() {
            for var in clause.vars.iter() {
                let name = var.get_name();
                if !(var_map.get(&(name, !var.is_negated())).is_some()
                    && var_map.get(&(name, var.is_negated())).is_some())
                {
                    pures.push(var.clone());
                }
            }
        }
        pures
    }

    fn pure_literal_elimination(&self, assignments: &mut HashMap<T, bool>) {
        // pure literal elimination
        for var in self.pure_literals.iter() {
            if assignments.get(var.get_name()).is_none() {
                assignments.insert(var.get_name().clone(), !var.is_negated());
            }
        }
    }

    fn dpll(
        &mut self,
        assignments: &mut HashMap<T, bool>,
        satisfied_clauses: &mut Vec<Clause<T>>,
    ) -> bool {
        if self.formula.is_satisfied(assignments) {
            return true;
        } else if self.all_assigned(assignments) {
            return false;
        }
        // unit propogation
        self.unit_prop(assignments, satisfied_clauses);
        // pure literal elimination
        self.pure_literal_elimination(assignments);

        // branch splitting
        for clause in self.formula.clauses.iter() {
            for var in clause.vars.iter() {
                if assignments.get(var.get_name()).is_none() {
                    let mut left_branch_assignments = assignments.clone();
                    let mut right_branch_assignments = assignments.clone();
                    let mut left_branch_clauses = satisfied_clauses.clone();
                    let mut right_branch_clauses = satisfied_clauses.clone();
                    left_branch_assignments.insert(var.get_name().clone(), true);
                    right_branch_assignments.insert(var.get_name().clone(), false);
                    return self.dpll(&mut left_branch_assignments, &mut left_branch_clauses)
                        || self.dpll(&mut right_branch_assignments, &mut right_branch_clauses);
                }
            }
        }

        // at this point there are no more unassigned vars, so we check
        // if the formula is satisfied
        self.dpll(assignments, satisfied_clauses)
    }

    pub fn run(mut self) -> bool {
        let mut assignments = HashMap::new();
        let mut satisfied_clauses = Vec::new();
        let res = self.dpll(&mut assignments, &mut satisfied_clauses);
        res
    }
}

#[cfg(test)]
mod sat_test {
    use crate::sat::{
        defs::{Clause, Formula, Lit},
        dimacs::parse_formula_from_dimacs_str,
    };

    use super::Solver;

    #[test]
    fn unsat_simple() {
        let var = Lit::pos("a");
        let var_neg = Lit::neg("a");
        let clause = Clause::new(vec![var]);
        let clause_neg = Clause::new(vec![var_neg]);
        let formula = Formula::new(vec![clause, clause_neg]);
        assert_eq!(Solver::new(formula).run(), false)
    }

    #[test]
    fn sat_single_var() {
        let var = Lit::pos("a");
        let clause = Clause::new(vec![var]);
        let formula = Formula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_single_var_negated() {
        let var = Lit::neg("a");
        let clause = Clause::new(vec![var]);
        let formula = Formula::new(vec![clause]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_neg_unit_prop() {
        let var1 = Lit::pos("a");
        let var1_neg = Lit::neg("a");
        let var2 = Lit::pos("b");
        let clause1 = Clause::new(vec![var1_neg]);
        let clause2 = Clause::new(vec![var1, var2]);
        let formula = Formula::new(vec![clause1, clause2]);
        assert_eq!(Solver::new(formula).run(), true)
    }

    #[test]
    fn sat_complex() {
        // (a ∨ ¬b ∨ c) ∧ (¬a ∨ b ∨ ¬d) ∧ (c ∨ d ∨ ¬e) ∧ (¬c ∨ ¬d ∨ e) ∧ (b ∨ ¬e ∨ ¬f) ∧ (¬b ∨ f ∨ a)
        let a = Lit::pos("a");
        let neg_b = Lit::neg("b");
        let c = Lit::pos("c");
        let clause1 = Clause::new(vec![a, neg_b, c]);

        let neg_a = Lit::neg("a");
        let b = Lit::pos("b");
        let neg_d = Lit::neg("d");
        let clause2 = Clause::new(vec![neg_a, b, neg_d]);

        let neg_e = Lit::neg("e");
        let d = Lit::pos("d");
        let clause3 = Clause::new(vec![c, d, neg_e]);

        let e = Lit::pos("e");
        let neg_c = Lit::neg("c");
        let clause4 = Clause::new(vec![neg_c, neg_d, e]);

        let neg_f = Lit::neg("f");
        let clause5 = Clause::new(vec![b, neg_e, neg_f]);

        let f = Lit::pos("a");
        let clause6 = Clause::new(vec![neg_b, f, a]);

        let formula = Formula::new(vec![clause1, clause2, clause3, clause4, clause5, clause6]);
        assert_eq!(Solver::new(formula).run(), true);
    }

    #[test]
    fn unsat_complex() {
        // (𝑥∨𝑦∨𝑧) ∧ (𝑥∨𝑦∨¬𝑧) ∧ (𝑥∨¬𝑦∨𝑧) ∧ (𝑥∨¬𝑦∨¬𝑧) ∧ (¬𝑥∨𝑦∨𝑧) ∧ (¬𝑥∨𝑦∨¬𝑧) ∧ (¬𝑥∨¬𝑦∨𝑧) ∧ (¬𝑥∨¬𝑦∨¬𝑧)
        let x = Lit::pos("x");
        let y = Lit::pos("y");
        let z = Lit::pos("z");
        let clause1 = Clause::new(vec![x, y, z]);
        let neg_z = Lit::neg("z");
        let clause2 = Clause::new(vec![x, y, neg_z]);
        let neg_y = Lit::neg("y");
        let clause3 = Clause::new(vec![x, neg_y, z]);
        let clause4 = Clause::new(vec![x, neg_y, neg_z]);
        let neg_x = Lit::neg("x");
        let clause5 = Clause::new(vec![neg_x, y, z]);
        let clause6 = Clause::new(vec![neg_x, y, neg_z]);
        let clause7 = Clause::new(vec![neg_x, neg_y, z]);
        let clause8 = Clause::new(vec![neg_x, neg_y, neg_z]);
        let formula = Formula::new(vec![
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
        // 1 = true
        // 5 = true
        // 4 = false
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
}
