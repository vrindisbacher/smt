use super::clause::Clause;

use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Formula<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub clauses: Vec<Clause<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Formula<T> {
    pub fn new(clauses: Vec<Clause<T>>) -> Self {
        Self { clauses }
    }
}
