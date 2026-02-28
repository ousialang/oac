use crate::parser::{qualify_namespace_function_name, Expression, Statement};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum AstPathStyle {
    Ir,
    StructInvariants,
}

fn separator(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "/",
        AstPathStyle::StructInvariants => ".",
    }
}

fn join_path(prefix: &str, segment: &str, style: AstPathStyle) -> String {
    if prefix.is_empty() {
        segment.to_string()
    } else {
        format!("{prefix}{}{segment}", separator(style))
    }
}

fn expression_statement_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "expr",
        AstPathStyle::StructInvariants => "expr.expr",
    }
}

fn if_then_statement_segment(style: AstPathStyle, index: usize) -> String {
    match style {
        AstPathStyle::Ir => format!("if.body.{index}"),
        AstPathStyle::StructInvariants => format!("if.then.{index}"),
    }
}

fn if_else_statement_segment(_style: AstPathStyle, index: usize) -> String {
    format!("if.else.{index}")
}

fn while_body_statement_segment(_style: AstPathStyle, index: usize) -> String {
    format!("while.body.{index}")
}

fn match_arm_statement_segment(
    _style: AstPathStyle,
    arm_index: usize,
    statement_index: usize,
) -> String {
    format!("match.arm.{arm_index}.{statement_index}")
}

fn match_arm_expression_segment(_style: AstPathStyle, arm_index: usize) -> String {
    format!("match.arm.{arm_index}")
}

fn bin_left_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "bin.left",
        AstPathStyle::StructInvariants => "bin.lhs",
    }
}

fn bin_right_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "bin.right",
        AstPathStyle::StructInvariants => "bin.rhs",
    }
}

fn unary_segment(style: AstPathStyle) -> &'static str {
    match style {
        AstPathStyle::Ir => "unary",
        AstPathStyle::StructInvariants => "unary.expr",
    }
}

fn struct_field_segment(style: AstPathStyle, index: usize, field_name: &str) -> String {
    match style {
        AstPathStyle::Ir => format!("struct.field.{index}"),
        AstPathStyle::StructInvariants => format!("struct.field.{field_name}"),
    }
}

pub(crate) fn walk_statement_expressions(
    statement: &Statement,
    statement_path: &str,
    style: AstPathStyle,
    on_expression: &mut impl FnMut(&str, &Expression),
) {
    match statement {
        Statement::StructDef { .. } => {}
        Statement::Assign { value, .. } => walk_expression(
            value,
            &join_path(statement_path, "assign.value", style),
            style,
            on_expression,
        ),
        Statement::Return { expr } => walk_expression(
            expr,
            &join_path(statement_path, "return.expr", style),
            style,
            on_expression,
        ),
        Statement::Expression { expr } => walk_expression(
            expr,
            &join_path(statement_path, expression_statement_segment(style), style),
            style,
            on_expression,
        ),
        Statement::Prove { condition } => walk_expression(
            condition,
            &join_path(statement_path, "prove.cond", style),
            style,
            on_expression,
        ),
        Statement::Assert { condition } => walk_expression(
            condition,
            &join_path(statement_path, "assert.cond", style),
            style,
            on_expression,
        ),
        Statement::Conditional {
            condition,
            body,
            else_body,
        } => {
            walk_expression(
                condition,
                &join_path(statement_path, "if.cond", style),
                style,
                on_expression,
            );
            for (index, nested) in body.iter().enumerate() {
                walk_statement_expressions(
                    nested,
                    &join_path(
                        statement_path,
                        &if_then_statement_segment(style, index),
                        style,
                    ),
                    style,
                    on_expression,
                );
            }
            if let Some(else_body) = else_body {
                for (index, nested) in else_body.iter().enumerate() {
                    walk_statement_expressions(
                        nested,
                        &join_path(
                            statement_path,
                            &if_else_statement_segment(style, index),
                            style,
                        ),
                        style,
                        on_expression,
                    );
                }
            }
        }
        Statement::While { condition, body } => {
            walk_expression(
                condition,
                &join_path(statement_path, "while.cond", style),
                style,
                on_expression,
            );
            for (index, nested) in body.iter().enumerate() {
                walk_statement_expressions(
                    nested,
                    &join_path(
                        statement_path,
                        &while_body_statement_segment(style, index),
                        style,
                    ),
                    style,
                    on_expression,
                );
            }
        }
        Statement::Match { subject, arms } => {
            walk_expression(
                subject,
                &join_path(statement_path, "match.subject", style),
                style,
                on_expression,
            );
            for (arm_index, arm) in arms.iter().enumerate() {
                for (statement_index, nested) in arm.body.iter().enumerate() {
                    walk_statement_expressions(
                        nested,
                        &join_path(
                            statement_path,
                            &match_arm_statement_segment(style, arm_index, statement_index),
                            style,
                        ),
                        style,
                        on_expression,
                    );
                }
            }
        }
    }
}

fn walk_expression(
    expression: &Expression,
    expression_path: &str,
    style: AstPathStyle,
    on_expression: &mut impl FnMut(&str, &Expression),
) {
    on_expression(expression_path, expression);

    match expression {
        Expression::Match { subject, arms } => {
            walk_expression(
                subject,
                &join_path(expression_path, "match.subject", style),
                style,
                on_expression,
            );
            for (index, arm) in arms.iter().enumerate() {
                walk_expression(
                    &arm.value,
                    &join_path(
                        expression_path,
                        &match_arm_expression_segment(style, index),
                        style,
                    ),
                    style,
                    on_expression,
                );
            }
        }
        Expression::Call(_, args) => {
            for (index, arg) in args.iter().enumerate() {
                walk_expression(
                    arg,
                    &join_path(expression_path, &format!("call.arg.{index}"), style),
                    style,
                    on_expression,
                );
            }
        }
        Expression::PostfixCall { callee, args } => {
            walk_expression(
                callee,
                &join_path(expression_path, "postfix.callee", style),
                style,
                on_expression,
            );
            for (index, arg) in args.iter().enumerate() {
                walk_expression(
                    arg,
                    &join_path(expression_path, &format!("postfix.arg.{index}"), style),
                    style,
                    on_expression,
                );
            }
        }
        Expression::BinOp(_, left, right) => {
            walk_expression(
                left,
                &join_path(expression_path, bin_left_segment(style), style),
                style,
                on_expression,
            );
            walk_expression(
                right,
                &join_path(expression_path, bin_right_segment(style), style),
                style,
                on_expression,
            );
        }
        Expression::UnaryOp(_, expr) => {
            walk_expression(
                expr,
                &join_path(expression_path, unary_segment(style), style),
                style,
                on_expression,
            );
        }
        Expression::StructValue { field_values, .. } => {
            for (index, (field_name, expr)) in field_values.iter().enumerate() {
                walk_expression(
                    expr,
                    &join_path(
                        expression_path,
                        &struct_field_segment(style, index, field_name),
                        style,
                    ),
                    style,
                    on_expression,
                );
            }
        }
        Expression::Literal(_) | Expression::Variable(_) | Expression::FieldAccess { .. } => {}
    }
}

pub(crate) fn walk_statement_calls(
    statement: &Statement,
    statement_path: &str,
    style: AstPathStyle,
    on_call: &mut impl FnMut(&str, &str),
) {
    walk_statement_expressions(
        statement,
        statement_path,
        style,
        &mut |expression_path, expression| match expression {
            Expression::Call(name, _) => on_call(expression_path, name),
            Expression::PostfixCall { callee, .. } => {
                if let Expression::FieldAccess {
                    struct_variable,
                    field,
                } = callee.as_ref()
                {
                    let namespaced_call = qualify_namespace_function_name(struct_variable, field);
                    on_call(expression_path, &namespaced_call);
                }
            }
            _ => {}
        },
    );
}
