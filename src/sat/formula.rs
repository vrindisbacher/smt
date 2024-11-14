use super::clause::CnfClause;
use crate::var::IntoCnf;
use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub(crate) struct CnfFormula<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub clauses: Vec<CnfClause<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoCnf<T> for CnfFormula<T> {
    fn into_cnf(self) -> CnfFormula<T> {
        self
    }
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> CnfFormula<T> {
    pub fn new(clauses: Vec<CnfClause<T>>) -> Self {
        Self { clauses }
    }
}
