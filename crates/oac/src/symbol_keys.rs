pub(crate) fn trait_method_key(trait_name: &str, method_name: &str) -> String {
    format!("{trait_name}::{method_name}")
}

pub(crate) fn trait_impl_target_key(trait_name: &str, for_type: &str) -> String {
    format!("{trait_name}::{for_type}")
}

pub(crate) fn trait_impl_method_key(trait_name: &str, for_type: &str, method_name: &str) -> String {
    format!("{trait_name}::{for_type}::{method_name}")
}

fn mangle_symbol_component(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

pub(crate) fn trait_impl_function_name(
    trait_name: &str,
    for_type: &str,
    method_name: &str,
) -> String {
    format!(
        "{}__{}__{}",
        trait_name,
        mangle_symbol_component(for_type),
        method_name
    )
}
