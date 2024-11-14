use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

use super::assignment::Assignments;
use super::formula::CnfFormula;
use crate::var::Lit;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CnfClause<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub vars: Vec<Lit<T>>,
    pub watchlist: Vec<usize>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> CnfClause<T> {
    pub fn new(vars: Vec<Lit<T>>) -> Self {
        let watchlist;
        if vars.len() >= 2 {
            watchlist = vec![0, 1];
        } else {
            watchlist = vec![0]
        }
        Self { vars, watchlist }
    }

    pub(crate) fn is_watching_at_least_one_true(&self, assignment: &Assignments<T>) -> bool {
        for idx in self.watchlist.iter() {
            if let Some(assn) = assignment.get_assignment(&self.vars[*idx]) {
                if assn {
                    return true;
                }
            }
        }
        false
    }

    pub(crate) fn resolve_watch(
        &self,
        formula: &mut CnfFormula<T>,
        lit_to_change: &Lit<T>,
        assignment: &mut Assignments<T>,
    ) -> Result<(), ()> {
        let to_change_idxs = self
            .watchlist
            .iter()
            .enumerate()
            .find(|(_, idx)| self.vars[**idx] == *lit_to_change);
        if let Some((to_change_wl_idx, idx_to_change)) = to_change_idxs {
            // now determine is we're looking at 2 vars or 1
            let mut other_idx = None;
            if self.watchlist.len() == 2 {
                other_idx = Some(self.watchlist[1 - to_change_wl_idx]);
            }
            let mut new_idx = -1;
            for (idx, var) in self.vars.iter().enumerate() {
                if idx == *idx_to_change
                    || other_idx.is_some_and(|other_idx: usize| other_idx == idx)
                {
                    continue;
                }
                if let Some(assn) = assignment.get_assignment(var) {
                    if assn {
                        new_idx = idx as i32;
                    }
                } else {
                    new_idx = idx as i32;
                }
            }
            if new_idx == -1 {
                if let Some(other_idx) = other_idx {
                    let other_watched = &self.vars[other_idx];
                    if let Some(assn) = assignment.get_assignment(other_watched) {
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
                // updates done to main formula clauses - at this point these are cloned
                formula.update_clause_watchlist(self, to_change_wl_idx, new_idx as usize);
                formula.remove_watching_clause_for_var(lit_to_change, self);
                formula.add_watching_clause_for_var(&self.vars[new_idx as usize], self);
            }
            Ok(())
        } else {
            Err(())
        }
    }
}
