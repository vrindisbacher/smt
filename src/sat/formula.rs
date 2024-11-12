use super::clause::Clause;

use std::clone::Clone;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone)]
pub struct Formula<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub clauses: Vec<Clause<T>>,
    // var name to index of clauses in formula...
    pub watched_by_map: HashMap<T, Vec<usize>>,
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

    fn create_watchlist_map(clauses: &Vec<Clause<T>>) -> HashMap<T, Vec<usize>> {
        let mut map = HashMap::new();
        for (idx, clause) in clauses.iter().enumerate() {
            for watch_idx in clause.watchlist.iter() {
                let var_name = clause.vars[*watch_idx].get_name().clone();
                map.entry(var_name)
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

    pub fn remove_watching_clause_for_var(&mut self, var_name: &T, clause: &Clause<T>) {
        self.watched_by_map.entry(var_name.clone()).and_modify(|e| {
            if let Some(idx) = e.iter().position(|i| self.clauses[*i] == *clause) {
                e.remove(idx);
            }
        });
    }

    pub fn add_watching_clause_for_var(&mut self, var_name: &T, clause: &Clause<T>) {
        if let Some(clause_idx) = self.clauses.iter().position(|c| c == clause) {
            self.watched_by_map.entry(var_name.clone()).and_modify(|e| {
                if !e.contains(&clause_idx) {
                    e.push(clause_idx);
                }
            });
        }
    }

    pub fn get_watching_clauses_for_var(&self, var_name: &T) -> Vec<Clause<T>> {
        let mut vec = vec![];
        if let Some(clause_idxs) = self.watched_by_map.get(var_name) {
            for idx in clause_idxs {
                let clause = self.clauses[*idx].clone();
                vec.push(clause);
            }
        }
        vec
    }
}
