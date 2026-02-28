#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ExternCallModel {
    Malloc,
    Free,
    Calloc,
    Realloc,
    Memcpy,
    Memset,
    Memmove,
    Memcmp,
    Strlen,
    Strcmp,
    Strcpy,
    Strncpy,
    Open,
    Read,
    Write,
    Close,
    Exit,
    Printf,
}

impl ExternCallModel {
    pub(crate) fn min_arity(self) -> usize {
        match self {
            ExternCallModel::Printf => 1,
            _ => self.exact_arity().expect("non-variadic arity exists"),
        }
    }

    pub(crate) fn exact_arity(self) -> Option<usize> {
        match self {
            ExternCallModel::Malloc => Some(1),
            ExternCallModel::Free => Some(1),
            ExternCallModel::Calloc => Some(2),
            ExternCallModel::Realloc => Some(2),
            ExternCallModel::Memcpy => Some(3),
            ExternCallModel::Memset => Some(3),
            ExternCallModel::Memmove => Some(3),
            ExternCallModel::Memcmp => Some(3),
            ExternCallModel::Strlen => Some(1),
            ExternCallModel::Strcmp => Some(2),
            ExternCallModel::Strcpy => Some(2),
            ExternCallModel::Strncpy => Some(3),
            ExternCallModel::Open => Some(3),
            ExternCallModel::Read => Some(3),
            ExternCallModel::Write => Some(3),
            ExternCallModel::Close => Some(1),
            ExternCallModel::Exit => Some(1),
            ExternCallModel::Printf => None,
        }
    }
}

pub(crate) fn extern_call_model(function: &str) -> Option<ExternCallModel> {
    match function {
        "malloc" => Some(ExternCallModel::Malloc),
        "free" => Some(ExternCallModel::Free),
        "calloc" => Some(ExternCallModel::Calloc),
        "realloc" => Some(ExternCallModel::Realloc),
        "memcpy" => Some(ExternCallModel::Memcpy),
        "memset" => Some(ExternCallModel::Memset),
        "memmove" => Some(ExternCallModel::Memmove),
        "memcmp" => Some(ExternCallModel::Memcmp),
        "strlen" => Some(ExternCallModel::Strlen),
        "strcmp" => Some(ExternCallModel::Strcmp),
        "strcpy" => Some(ExternCallModel::Strcpy),
        "strncpy" => Some(ExternCallModel::Strncpy),
        "open" => Some(ExternCallModel::Open),
        "read" => Some(ExternCallModel::Read),
        "write" => Some(ExternCallModel::Write),
        "close" => Some(ExternCallModel::Close),
        "exit" => Some(ExternCallModel::Exit),
        "printf" => Some(ExternCallModel::Printf),
        _ => None,
    }
}

pub(crate) fn call_is_exit(function: &str) -> bool {
    extern_call_model(function) == Some(ExternCallModel::Exit)
}
