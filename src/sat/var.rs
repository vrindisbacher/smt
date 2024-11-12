use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Var<T: PartialEq + Eq + Hash + Debug + Clone> {
    name: T,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Var<T> {
    pub fn new(name: T) -> Self {
        Self { name }
    }

    pub fn get_name(&self) -> &T {
        &self.name
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Lit<T: PartialEq + Eq + Hash + Debug + Clone> {
    negated: bool,
    var: Var<T>,
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Lit<T> {
    pub fn pos(var: Var<T>) -> Self {
        Self {
            var,
            negated: false,
        }
    }

    pub fn neg(var: Var<T>) -> Self {
        Self { var, negated: true }
    }

    pub fn get_var(&self) -> &Var<T> {
        &self.var
    }

    pub fn get_name(&self) -> &T {
        &self.var.get_name()
    }

    pub fn is_negated(&self) -> bool {
        self.negated
    }
}
