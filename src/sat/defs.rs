use std::collections::HashMap;

#[derive(Clone, Copy, Debug)]
pub struct Var<'a> {
    name: &'a str,
    negated: bool,
}

impl<'a> Var<'a> {
    pub fn new(name: &'a str) -> Self {
        Self {
            name,
            negated: false,
        }
    }

    pub fn negated(name: &'a str) -> Self {
        Self {
            name,
            negated: true,
        }
    }

    pub fn get_name(&self) -> &'a str {
        &self.name
    }

    pub fn is_negated(&self) -> bool {
        self.negated
    }
}

#[derive(Debug, Clone)]
pub struct Clause<'a> {
    pub vars: Vec<Var<'a>>,
}

impl<'a> Clause<'a> {
    pub fn new(vars: Vec<Var<'a>>) -> Self {
        Self { vars }
    }

    pub fn get_unit_var(&self, assignments: &HashMap<&'a str, bool>) -> Option<&Var<'a>> {
        // exactly one unassigned variable in clause makes it a unit
        let unassigned_vars: Vec<&Var<'a>> = self
            .vars
            .iter()
            .flat_map(|var| {
                if assignments.get(var.name).is_none() {
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

    pub fn is_satified(&'a self, assignments: &'a HashMap<&'a str, bool>) -> bool {
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
pub struct Formula<'a> {
    pub clauses: Vec<Clause<'a>>,
}

impl<'a> Formula<'a> {
    pub fn new(clauses: Vec<Clause<'a>>) -> Self {
        Self { clauses }
    }

    pub fn is_satisfied(&'a self, assignments: &'a HashMap<&'a str, bool>) -> bool {
        for clause in self.clauses.iter() {
            if !clause.is_satified(assignments) {
                return false;
            }
        }
        true
    }
}
