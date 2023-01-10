//! An implementation of a `Visitor` which prints the structure of the AST

use super::visit::{Visitable, Visitor};

/// Visit the given AST fragment and output its pretty printed equivalent
pub fn print(ast: impl Visitable) -> String {
    let mut printer = Printer;
    ast.visit_with(&mut printer)
}

/// The AST printer
#[derive(Debug)]
pub struct Printer;

impl Visitor for Printer {
    type Output = String;

    fn default_output(&self) -> Self::Output {
        String::new()
    }

    fn combine_output(&self, mut o1: Self::Output, o2: Self::Output) -> Self::Output {
        o1.push_str(&o2);

        o1
    }

    fn visit_binary_expr(&mut self, d: &super::BinaryExpr) -> Self::Output {
        let super::BinaryExpr {
            left,
            right,
            operator,
        } = d;

        let o1 = left.visit_with(self);
        let o2 = right.visit_with(self);

        format!("({operator} {o1} {o2})")
    }

    fn visit_grouping_expr(&mut self, d: &super::GroupingExpr) -> Self::Output {
        let super::GroupingExpr { inner } = d;

        let o = inner.visit_with(self);

        format!("(group {o})")
    }

    fn visit_literal_expr(&mut self, d: &super::LiteralExpr) -> Self::Output {
        d.to_string()
    }

    fn visit_unary_expr(&mut self, d: &super::UnaryExpr) -> Self::Output {
        let super::UnaryExpr { operator, right } = d;

        let o = right.visit_with(self);

        format!("({operator} {o})")
    }

    fn visit_logical_expr(&mut self, d: &super::LogicalExpr) -> Self::Output {
        let super::LogicalExpr {
            left,
            right,
            operator,
        } = d;

        let ol = left.visit_with(self);
        let or = right.visit_with(self);

        format!("({} {ol} {or})", operator.symbol())
    }

    fn visit_assign_expr(&mut self, d: &super::AssignExpr) -> Self::Output {
        let super::AssignExpr { name, value } = d;

        let value = value.visit_with(self);

        format!("(= {name} {value})")
    }

    fn visit_var_expr(&mut self, d: &super::VarExpr) -> Self::Output {
        let super::VarExpr { name } = d;

        format!("(var {name})")
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        ast::{printer::print, *},
        span::Span,
    };
    use std::sync::Arc;

    #[test]
    fn print_simple_ast() {
        let ast = Expr {
            span: Span::dummy(),
            kind: BinaryExpr {
                left: Arc::new(Expr {
                    span: Span::dummy(),
                    kind: UnaryExpr {
                        operator: UnaryOpKind::Negate,
                        right: Arc::new(Expr {
                            span: Span::dummy(),
                            kind: LiteralExpr::Number(123.0).into(),
                        }),
                    }
                    .into(),
                }),
                operator: BinaryOpKind::Mult,
                right: Arc::new(Expr {
                    span: Span::dummy(),
                    kind: GroupingExpr {
                        inner: Arc::new(Expr {
                            span: Span::dummy(),
                            kind: LiteralExpr::Number(45.67).into(),
                        }),
                    }
                    .into(),
                }),
            }
            .into(),
        };

        let out = print(ast);

        assert_eq!(out, "(* (- 123) (group 45.67))")
    }
}
