use super::formula::{Expr, Int, QFLIAFormula};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

#[derive(Debug, Hash, PartialEq, Eq)]
pub(crate) enum NormExpr<T: Debug + Hash + PartialEq + Eq> {
    Const(Int<T>),
    Var(i128, Int<T>),
    Add(Box<NormExpr<T>>, Box<NormExpr<T>>),
}

#[derive(Debug, Hash, PartialEq, Eq)]
pub(crate) struct NormQFLIAFormula<T: Debug + Hash + PartialEq + Eq> {
    pub lhs: NormExpr<T>,
    pub rhs: i128,
}

pub(crate) struct QFLIAExprToSimpleCompiler<T: Debug + Hash + PartialEq + Eq> {
    const_acc: i128,
    var_acc: HashMap<T, i128>,
}

impl<T: Debug + Hash + PartialEq + Eq> QFLIAExprToSimpleCompiler<T> {
    fn collect_atoms<'a>(&mut self, expr: Expr<T>) {
        match expr {
            Expr::Atom(x) => match x {
                Int::Const(i) => {
                    self.const_acc += i;
                }
                Int::Var(v) => {
                    self.var_acc
                        .entry(v)
                        .and_modify(|sum| *sum += 1)
                        .or_insert(1);
                }
            },
            Expr::Mul(x, expr) => {
                // because of calling simplify which calls distribute -> we can guarantee that
                // mul is right next to a var so we can just insert it
                match *expr {
                    Expr::Atom(Int::Var(name)) => {
                        self.var_acc
                            .entry(name)
                            .and_modify(|sum| *sum += x)
                            .or_insert(x);
                    }
                    _ => {
                        panic!("Unexpected value in mul after distributing")
                    }
                }
            }
            Expr::Add(lhs, rhs) => {
                self.collect_atoms(*lhs);
                self.collect_atoms(*rhs);
            }
        }
    }

    fn var_acc_into_expr(self) -> NormExpr<T> {
        let mut as_list = self.var_acc.into_iter();
        let (term, coeff) = as_list.next().unwrap();
        let expr = if coeff == 0 {
            NormExpr::Const(Int::from_const(0))
        } else if coeff == 1 {
            NormExpr::Const(Int::from_var(term))
        } else {
            NormExpr::Var(coeff, Int::from_var(term))
        };
        as_list.skip(1).fold(expr, |acc, (term, coeff)| {
            if coeff == 0 {
                acc
            } else if coeff == 1 {
                NormExpr::Add(
                    Box::new(acc),
                    Box::new(NormExpr::Const(Int::from_var(term))),
                )
            } else {
                NormExpr::Add(
                    Box::new(acc),
                    Box::new(NormExpr::Var(coeff, Int::from_var(term))),
                )
            }
        })
    }

    fn normalize(mut self, expr: Expr<T>) -> NormQFLIAFormula<T> {
        // at this point, everything is already in the simplest form because we've distributed
        // all multiplication - we just have addition and we can use the commutative property
        // to simplify as we please
        self.collect_atoms(expr);
        if self.var_acc.len() > 0 {
            // put const on the rhs - need to subtract it obviously 
            NormQFLIAFormula {
                rhs: -self.const_acc,
                lhs: self.var_acc_into_expr(),
            }
        } else {
            NormQFLIAFormula {
                rhs: 0,
                lhs: NormExpr::Const(Int::from_const(0)),
            }
        }
    }

    pub fn new() -> Self {
        Self {
            var_acc: HashMap::new(),
            const_acc: 0,
        }
    }

    pub fn run(self, expr: QFLIAFormula<T>) -> NormQFLIAFormula<T> {
        self.normalize(expr.expr.distribute(1))
    }
}
