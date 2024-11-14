use std::clone::Clone;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

use crate::sat::clause::CnfClause;
use crate::sat::formula::CnfFormula;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PropOp {
    And,
    Or,
    Implies,
    Iff,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Prop<T: PartialEq + Eq + Hash + Debug + Clone> {
    Lit(Lit<T>),
    Prop(Box<Prop<T>>, Box<Prop<T>>, PropOp),
}

pub trait IntoProp<T: PartialEq + Eq + Hash + Debug + Clone> {
    fn into_prop(self) -> Prop<T>;
}

pub(crate) trait IntoCnf<T: PartialEq + Eq + Hash + Debug + Clone> {
    fn into_cnf(self) -> CnfFormula<T>;
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoProp<T> for Prop<T> {
    fn into_prop(self) -> Prop<T> {
        self
    }
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoCnf<T> for Prop<T> {
    fn into_cnf(self) -> CnfFormula<T> {
        self.into_cnf()
    }
}

impl<T: PartialEq + Eq + Hash + Debug + Clone> Prop<T> {
    pub(crate) fn singular(lit: Lit<T>) -> Self {
        Self::Lit(lit)
    }

    pub(crate) fn prop(lhs: Prop<T>, rhs: Prop<T>, op: PropOp) -> Self {
        Self::Prop(Box::new(lhs), Box::new(rhs), op)
    }

    // pub fn negate(self) -> Self {
    //     match self {
    //         FirstOrderProp::Lit(lit) => {
    //             if lit.is_negated() {
    //                 FirstOrderProp::Lit(Lit::pos(lit.get_var_owned()))
    //             } else {
    //                 FirstOrderProp::Lit(Lit::neg(lit.get_var_owned()))
    //             }
    //         }
    //         FirstOrderProp::Prop(lhs, rhs, first_order_op) => {
    //             let lhs = lhs.negate();
    //             let rhs = rhs.negate();
    //             match first_order_op {
    //                 FirstOrderOp::And => {
    //                     FirstOrderProp::Prop(Box::new(lhs), Box::new(rhs), FirstOrderOp::Or)
    //                 }
    //                 FirstOrderOp::Or => {
    //                     FirstOrderProp::Prop(Box::new(lhs), Box::new(rhs), FirstOrderOp::And)
    //                 }
    //                 FirstOrderOp::Implies => {
    //                     // here we need to negate the lhs and then connect with an or. EX:
    //                     //
    //                     // not ( x => y )
    //                     // not ( not x or y )
    //                     // x and not y
    //                     FirstOrderProp::Prop(
    //                         Box::new(lhs.negate()),
    //                         Box::new(rhs),
    //                         FirstOrderOp::And,
    //                     )
    //                 }
    //                 FirstOrderOp::Iff => {
    //                     // Ex:
    //                     // not (x <=> y)
    //                     // not (x -> y /\ y -> x)
    //                     // not ((not x or y) /\ (not y or x))
    //                     // not (not x or y) \/ not (not y or x)
    //                     // x and not y \/ y or not x
    //                     let lhs_negated = lhs.clone().negate();
    //                     let rhs_negated = rhs.clone().negate();
    //                     FirstOrderProp::Prop(
    //                         Box::new(FirstOrderProp::Prop(
    //                             Box::new(lhs_negated),
    //                             Box::new(rhs),
    //                             FirstOrderOp::And,
    //                         )),
    //                         Box::new(FirstOrderProp::Prop(
    //                             Box::new(rhs_negated),
    //                             Box::new(lhs),
    //                             FirstOrderOp::And,
    //                         )),
    //                         FirstOrderOp::Or,
    //                     )
    //                 }
    //             }
    //         }
    //     }
    // }

    // fn nnf(self) -> Self {
    //     match self {
    //         FirstOrderProp::Lit(lit) => FirstOrderProp::Lit(lit),
    //         FirstOrderProp::Prop(lhs, rhs, op) => match op {
    //             FirstOrderOp::Implies => FirstOrderProp::Prop(
    //                 Box::new(lhs.nnf().negate()),
    //                 Box::new(rhs.nnf()),
    //                 FirstOrderOp::Or,
    //             ),
    //             FirstOrderOp::Iff => FirstOrderProp::Prop(
    //                 Box::new(FirstOrderProp::Prop(
    //                     Box::new(lhs.clone().nnf().negate()),
    //                     Box::new(rhs.clone().nnf()),
    //                     FirstOrderOp::Or,
    //                 )),
    //                 Box::new(FirstOrderProp::Prop(
    //                     Box::new(rhs.nnf().negate()),
    //                     Box::new(lhs.nnf()),
    //                     FirstOrderOp::Or,
    //                 )),
    //                 FirstOrderOp::And,
    //             ),
    //             op => FirstOrderProp::Prop(Box::new(lhs.nnf()), Box::new(rhs.nnf()), op),
    //         },
    //     }
    // }

    fn collect_vars_helper<'a>(&'a self, vec: &mut Vec<&'a Var<T>>) {
        match self {
            Prop::Lit(lit) => {
                if !vec.contains(&lit.get_var()) {
                    vec.push(lit.get_var());
                }
            }
            Prop::Prop(lhs, rhs, _) => {
                lhs.collect_vars_helper(vec);
                rhs.collect_vars_helper(vec);
            }
        }
    }

    fn collect_vars(&self) -> Vec<&Var<T>> {
        let mut vec = Vec::new();
        self.collect_vars_helper(&mut vec);
        vec
    }

    fn check(&self, assignments: &mut HashMap<&T, bool>) -> bool {
        match self {
            Prop::Lit(x) => {
                return if x.is_negated() {
                    !assignments.get(&x.get_name()).unwrap()
                } else {
                    *assignments.get(&x.get_name()).unwrap()
                }
            }
            Prop::Prop(lhs, rhs, op) => match op {
                PropOp::And => lhs.check(assignments) && rhs.check(assignments),
                PropOp::Or => lhs.check(assignments) || rhs.check(assignments),
                PropOp::Implies => !lhs.check(assignments) || rhs.check(assignments),
                PropOp::Iff => {
                    (!lhs.check(assignments) || rhs.check(assignments))
                        && (!rhs.check(assignments) || lhs.check(assignments))
                }
            },
        }
    }

    pub(crate) fn into_cnf(self) -> CnfFormula<T> {
        // TODO(VR): Use this later
        //
        // turn all implications into not, or, and
        // let new = self.nnf();

        // Get a truth table
        let vars = self.collect_vars();
        let unsat_assignments: Vec<HashMap<&T, bool>> = (0..2u32.pow(vars.len() as u32))
            .flat_map(|n| {
                let mut assn = HashMap::new();
                for i in 0..vars.len() {
                    assn.insert(vars[i].get_name(), (n >> i) & 1 == 1);
                }
                if !self.check(&mut assn) {
                    Some(assn)
                } else {
                    None
                }
            })
            .collect();

        // invert the unsat assignments
        let mut clauses = Vec::new();
        for unsat_assn in unsat_assignments {
            let mut vars = Vec::new();
            for (var_name, assn) in unsat_assn {
                let lit;
                if assn {
                    lit = Lit::neg(Var::new(var_name.clone()));
                } else {
                    lit = Lit::pos(Var::new(var_name.clone()));
                }
                vars.push(lit)
            }
            clauses.push(CnfClause::new(vars));
        }
        CnfFormula::new(clauses)
    }

    pub fn implies(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Self::Prop(Box::new(self), Box::new(rhs.into_prop()), PropOp::Implies)
    }

    pub fn iff(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Self::Prop(Box::new(self), Box::new(rhs.into_prop()), PropOp::Iff)
    }

    pub fn or(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Self::Prop(Box::new(self), Box::new(rhs.into_prop()), PropOp::Or)
    }

    pub fn and(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Self::Prop(Box::new(self), Box::new(rhs.into_prop()), PropOp::And)
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

    pub fn implies(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Prop::prop(Prop::singular(self), rhs.into_prop(), PropOp::Implies)
    }

    pub fn iff(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Prop::prop(Prop::singular(self), rhs.into_prop(), PropOp::Iff)
    }

    pub fn or(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Prop::prop(Prop::singular(self), rhs.into_prop(), PropOp::Or)
    }

    pub fn and(self, rhs: impl IntoProp<T>) -> Prop<T> {
        Prop::prop(Prop::singular(self), rhs.into_prop(), PropOp::And)
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

impl<T: PartialEq + Eq + Hash + Debug + Clone> IntoProp<T> for Lit<T> {
    fn into_prop(self) -> Prop<T> {
        Prop::singular(self)
    }
}
