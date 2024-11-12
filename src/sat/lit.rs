use super::clause::Clause;
use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lit<T: PartialEq + Eq + Hash + Debug + Clone> {
    negated: bool,
    name: T,
    watched_by: Vec<Clause<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Lit<T> {
    pub fn pos(name: T) -> Self {
        Self {
            name,
            negated: false,
            watched_by: Vec::new(),
        }
    }

    pub fn neg(name: T) -> Self {
        Self {
            name,
            negated: true,
            watched_by: Vec::new(),
        }
    }

    pub fn get_name(&self) -> &T {
        &self.name
    }

    pub fn add_watched_by(&mut self, clause: Clause<T>) {
        self.watched_by.push(clause);
    }

    pub fn remove_watched_by(&mut self, clause: &Clause<T>) {
        let idx = self.watched_by.iter().position(|c| c == clause);
        if let Some(idx) = idx {
            self.watched_by.remove(idx);
        }
    }

    pub fn is_negated(&self) -> bool {
        self.negated
    }

    pub fn watching_clauses(&self) -> &Vec<Clause<T>> {
        &self.watched_by
    }

    pub fn watching_clauses_mut(&mut self) -> &mut Vec<Clause<T>> {
        &mut self.watched_by
    }
}
