use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

use crate::var::Lit;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CnfClause<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub vars: Vec<Lit<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> CnfClause<T> {
    pub fn new(vars: Vec<Lit<T>>) -> Self {
        Self { vars }
    }
}
