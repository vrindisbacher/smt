use std::clone::Clone;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit<T: PartialEq + Eq + Hash + Debug + Clone> {
    name: T,
    negated: bool,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Lit<T> {
    pub fn pos(name: T) -> Self {
        Self {
            name,
            negated: false,
        }
    }

    pub fn neg(name: T) -> Self {
        Self {
            name,
            negated: true,
        }
    }

    pub fn get_name(&self) -> &T {
        &self.name
    }

    pub fn is_negated(&self) -> bool {
        self.negated
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Clause<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub vars: Vec<Lit<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Clause<T> {
    pub fn new(vars: Vec<Lit<T>>) -> Self {
        Self { vars }
    }

    pub fn get_unit_var(&self, assignments: &HashMap<T, bool>) -> Option<&Lit<T>> {
        // exactly one unassigned variable in clause makes it a unit
        let unassigned_vars: Vec<&Lit<T>> = self
            .vars
            .iter()
            .flat_map(|var| {
                if assignments.get(&var.name).is_none() {
                    Some(var)
                } else {
                    None
                }
            })
            .collect();
        if unassigned_vars.len() == 1 {
            Some(unassigned_vars[0])
        } else {
            None
        }
    }

    pub fn is_satisfied(&self, assignments: &HashMap<T, bool>) -> bool {
        for var in self.vars.iter() {
            if let Some(assignment) = assignments.get(var.get_name()) {
                let literal_value = if var.is_negated() {
                    !*assignment
                } else {
                    *assignment
                };
                if literal_value {
                    return true;
                }
            }
        }
        false
    }
}

#[derive(Debug, Clone)]
pub struct Formula<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub clauses: Vec<Clause<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Formula<T> {
    pub fn new(clauses: Vec<Clause<T>>) -> Self {
        Self { clauses }
    }

    pub fn is_satisfied(&self, assignments: &HashMap<T, bool>) -> bool {
        for clause in self.clauses.iter() {
            if !clause.is_satisfied(assignments) {
                return false;
            }
        }
        true
    }
}
