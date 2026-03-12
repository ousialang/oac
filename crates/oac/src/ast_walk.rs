pub(crate) use crate::ast_paths::AstPathStyle;
use crate::ast_paths::{
    bin_left_segment, bin_right_segment, expression_statement_segment, if_else_statement_segment,
    if_then_statement_segment, join_path, match_arm_expression_segment,
    match_arm_statement_segment, struct_field_segment, unary_segment, while_body_statement_segment,
};
use crate::parser::{qualify_namespace_function_name, Expression, Statement};

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

pub(crate) fn walk_expression_tree(
    expression: &Expression,
    expression_path: &str,
    style: AstPathStyle,
    on_expression: &mut impl FnMut(&str, &Expression),
) {
    walk_expression(expression, expression_path, style, on_expression);
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
        Expression::MethodCall {
            receiver,
            method: _,
            args,
        } => {
            walk_expression(
                receiver,
                &join_path(expression_path, "method.receiver", style),
                style,
                on_expression,
            );
            for (index, arg) in args.iter().enumerate() {
                walk_expression(
                    arg,
                    &join_path(expression_path, &format!("method.arg.{index}"), style),
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
            Expression::MethodCall { .. } => {}
            _ => {}
        },
    );
}
