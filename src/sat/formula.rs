use super::assignment;
use super::clause::Clause;
use super::var::Lit;

use std::clone::Clone;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Formula<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub clauses: Vec<Clause<T>>,
    // var name and negation to index of clauses in formula...
    pub watched_by_map: HashMap<(T, bool), Vec<usize>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Formula<T> {
    pub fn new(clauses: Vec<Clause<T>>) -> Self {
        // do some preprocessing for clauses
        let watched_by_map = Self::create_watchlist_map(&clauses);
        Self {
            clauses,
            watched_by_map,
        }
    }

    fn create_watchlist_map(clauses: &Vec<Clause<T>>) -> HashMap<(T, bool), Vec<usize>> {
        let mut map = HashMap::new();
        for (idx, clause) in clauses.iter().enumerate() {
            for watch_idx in clause.watchlist.iter() {
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

    pub fn remove_watching_clause_for_var(&mut self, lit: &Lit<T>, clause: &Clause<T>) {
        self.watched_by_map
            .entry((lit.get_name().clone(), lit.is_negated()))
            .and_modify(|e| {
                if let Some(idx) = e.iter().position(|i| self.clauses[*i].vars == *clause.vars) {
                    e.remove(idx);
                }
            });
    }

    pub fn add_watching_clause_for_var(&mut self, lit: &Lit<T>, clause: &Clause<T>) {
        if let Some(clause_idx) = self.clauses.iter().position(|c| c.vars == clause.vars) {
            self.watched_by_map
                .entry((lit.get_name().clone(), lit.is_negated()))
                .and_modify(|e| {
                    if !e.contains(&clause_idx) {
                        e.push(clause_idx);
                    }
                });
        }
    }

    pub fn get_watching_clauses_for_var(&self, lit: &Lit<T>) -> Vec<Clause<T>> {
        let mut vec = vec![];
        if let Some(clause_idxs) = self
            .watched_by_map
            .get(&(lit.get_name().clone(), lit.is_negated()))
        {
            for idx in clause_idxs {
                let clause = self.clauses[*idx].clone();
                vec.push(clause);
            }
        }
        vec
    }

    pub fn update_clause_watchlist(
        &mut self,
        clause: &Clause<T>,
        to_change_wl_idx: usize,
        new_idx: usize,
    ) {
        if let Some(clause_to_update_idx) =
            self.clauses.iter_mut().position(|c| c.vars == clause.vars)
        {
            self.clauses[clause_to_update_idx].watchlist[to_change_wl_idx] = new_idx;
        }
    }
}
