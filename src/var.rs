use std::clone::Clone;
use std::fmt::Debug;
use std::hash::Hash;

pub enum FirstOrderOp {
    And,
    Or,
    Implies,
    Iff,
}

pub enum FirstOrderProp<T: PartialEq + Eq + Hash + Debug + Clone> {
    Lit(Lit<T>),
    Prop(Box<FirstOrderProp<T>>, Box<FirstOrderProp<T>>, FirstOrderOp),
}

pub trait IntoFirstOrder<T: PartialEq + Eq + Hash + Debug + Clone> {
    fn into_first_order_prop(self) -> FirstOrderProp<T>;
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoFirstOrder<T> for FirstOrderProp<T> {
    fn into_first_order_prop(self) -> FirstOrderProp<T> {
        self
    }
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> FirstOrderProp<T> {
    pub(crate) fn singular(lit: Lit<T>) -> Self {
        Self::Lit(lit)
    }

    pub(crate) fn prop(lhs: FirstOrderProp<T>, rhs: FirstOrderProp<T>, op: FirstOrderOp) -> Self {
        Self::Prop(Box::new(lhs), Box::new(rhs), op)
    }

    pub fn implies(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        Self::Prop(
            Box::new(self),
            Box::new(rhs.into_first_order_prop()),
            FirstOrderOp::Implies,
        )
    }

    pub fn iff(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        Self::Prop(
            Box::new(self),
            Box::new(rhs.into_first_order_prop()),
            FirstOrderOp::Iff,
        )
    }

    pub fn or(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        Self::Prop(
            Box::new(self),
            Box::new(rhs.into_first_order_prop()),
            FirstOrderOp::Or,
        )
    }

    pub fn and(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        Self::Prop(
            Box::new(self),
            Box::new(rhs.into_first_order_prop()),
            FirstOrderOp::And,
        )
    }
}

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

    pub fn implies(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        FirstOrderProp::prop(
            FirstOrderProp::singular(self),
            rhs.into_first_order_prop(),
            FirstOrderOp::Implies,
        )
    }

    pub fn iff(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        FirstOrderProp::prop(
            FirstOrderProp::singular(self),
            rhs.into_first_order_prop(),
            FirstOrderOp::Iff,
        )
    }

    pub fn or(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        FirstOrderProp::prop(
            FirstOrderProp::singular(self),
            rhs.into_first_order_prop(),
            FirstOrderOp::Or,
        )
    }

    pub fn and(self, rhs: impl IntoFirstOrder<T>) -> FirstOrderProp<T> {
        FirstOrderProp::prop(
            FirstOrderProp::singular(self),
            rhs.into_first_order_prop(),
            FirstOrderOp::And,
        )
    }

    pub fn neg(var: Var<T>) -> Self {
        Self { var, negated: true }
    }

    pub(crate) fn is_negated(&self) -> bool {
        self.negated
    }

    pub(crate) fn get_var(&self) -> &Var<T> {
        &self.var
    }

    pub(crate) fn get_name(&self) -> &T {
        &self.var.get_name()
    }
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoFirstOrder<T> for Lit<T> {
    fn into_first_order_prop(self) -> FirstOrderProp<T> {
        FirstOrderProp::singular(self)
    }
}
