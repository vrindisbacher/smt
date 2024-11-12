use std::clone::Clone;
use std::collections::{HashMap, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;

use super::var::{Lit, Var};

#[derive(Debug)]
pub struct Assignments<T: PartialEq + Eq + Hash + Debug + Clone> {
    pub assignments_stack: Vec<(HashMap<T, bool>, Option<Var<T>>)>,
    pub propogation_queue: VecDeque<Lit<T>>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Assignments<T> {
    pub fn new() -> Self {
        let new_assignments = HashMap::new();
        Self {
            assignments_stack: vec![(new_assignments, None)],
            propogation_queue: VecDeque::new(),
        }
    }

    pub fn get_assignment(&self, var: &Lit<T>) -> Option<bool> {
        // use the most recent assignment stack
        self.assignments_stack
            .last()?
            .0
            .get(&var.get_name())
            .and_then(|x: &bool| if var.is_negated() { Some(!x) } else { Some(*x) })
    }

    pub fn assign(&mut self, var: T, val: bool) {
        let assignments = self.assignments_stack.last_mut().unwrap();
        assignments.0.insert(var.clone(), val);
        if val {
            self.propogation_queue.push_back(Lit::neg(Var::new(var)));
        } else {
            self.propogation_queue.push_back(Lit::pos(Var::new(var)));
        }
    }

    pub fn create_decision_level(&mut self, var: &Var<T>, assn: bool) {
        let mut new_assignment_map = self.assignments_stack.last().unwrap().clone().0;
        new_assignment_map.insert(var.get_name().clone(), assn);
        self.assignments_stack
            .push((new_assignment_map, Some(var.clone())));
        if assn {
            self.propogation_queue.push_back(Lit::neg(var.clone()));
        } else {
            self.propogation_queue.push_back(Lit::pos(var.clone()));
        }
    }

    pub fn backtrack(&mut self) -> (Var<T>, bool) {
        let stack_frame = self
            .assignments_stack
            .pop()
            .expect("Cannot backtrack with empty stack");
        let var = stack_frame.1.unwrap();
        let assn = stack_frame
            .0
            .get(var.get_name())
            .expect("Must be assigned here");
        (var, *assn)
    }
}
