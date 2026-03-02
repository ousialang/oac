use std::collections::{BTreeMap, HashMap, HashSet};

use anyhow::{bail, Context};

use crate::builtins::BuiltInType;
use crate::ir::{self, FunctionSignature, ResolvedProgram, TypeDef};
use crate::parser::{self, Op, UnaryOp};
use crate::runtime_layout;
use crate::symbol_keys::{trait_impl_method_key, trait_method_key};

const ASSERT_FAILURE_EXIT_CODE: u64 = 242;
const INTEGER_FMT_GLOBAL: &str = "integer_fmt";
const PRINT_STR_NEWLINE_GLOBAL: &str = "print_str_newline";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LlvmType {
    I32,
    I64,
    Float,
    Double,
    Void,
}

impl LlvmType {
    fn as_ir(self) -> &'static str {
        match self {
            LlvmType::I32 => "i32",
            LlvmType::I64 => "i64",
            LlvmType::Float => "float",
            LlvmType::Double => "double",
            LlvmType::Void => "void",
        }
    }

    fn align(self) -> u32 {
        match self {
            LlvmType::I32 | LlvmType::Float => 4,
            LlvmType::I64 | LlvmType::Double => 8,
            LlvmType::Void => 1,
        }
    }

    fn is_float(self) -> bool {
        matches!(self, LlvmType::Float | LlvmType::Double)
    }
}

#[derive(Clone, Debug)]
struct ExternSig {
    ret: LlvmType,
    args: Vec<LlvmType>,
    variadic: bool,
}

#[derive(Clone, Debug)]
struct VarSlot {
    slot: String,
    ty: String,
}

#[derive(Clone, Debug)]
struct ExprValue {
    ty: String,
    llvm_ty: LlvmType,
    repr: String,
}

#[derive(Default)]
struct ModuleEmitter<'a> {
    program: Option<&'a ResolvedProgram>,
    user_function_texts: Vec<String>,
    extern_sigs: BTreeMap<String, ExternSig>,
    string_literal_names: HashMap<Vec<u8>, String>,
    string_literal_defs: Vec<(String, Vec<u8>)>,
    next_string_literal_id: usize,
}

impl<'a> ModuleEmitter<'a> {
    fn new(program: &'a ResolvedProgram) -> anyhow::Result<Self> {
        let mut emitter = Self {
            program: Some(program),
            ..Self::default()
        };
        emitter.seed_runtime_externs();
        emitter.collect_user_extern_signatures()?;
        Ok(emitter)
    }

    fn program(&self) -> &'a ResolvedProgram {
        self.program.expect("program should be available")
    }

    fn seed_runtime_externs(&mut self) {
        self.register_extern(
            "malloc",
            ExternSig {
                ret: LlvmType::I64,
                args: vec![LlvmType::I64],
                variadic: false,
            },
        )
        .expect("seed malloc extern");
        self.register_extern(
            "calloc",
            ExternSig {
                ret: LlvmType::I64,
                args: vec![LlvmType::I64, LlvmType::I64],
                variadic: false,
            },
        )
        .expect("seed calloc extern");
        self.register_extern(
            "memcpy",
            ExternSig {
                ret: LlvmType::I64,
                args: vec![LlvmType::I64, LlvmType::I64, LlvmType::I64],
                variadic: false,
            },
        )
        .expect("seed memcpy extern");
        self.register_extern(
            "memcmp",
            ExternSig {
                ret: LlvmType::I32,
                args: vec![LlvmType::I64, LlvmType::I64, LlvmType::I64],
                variadic: false,
            },
        )
        .expect("seed memcmp extern");
        self.register_extern(
            "printf",
            ExternSig {
                ret: LlvmType::I32,
                args: vec![LlvmType::I64],
                variadic: true,
            },
        )
        .expect("seed printf extern");
        self.register_extern(
            "write",
            ExternSig {
                ret: LlvmType::I64,
                args: vec![LlvmType::I32, LlvmType::I64, LlvmType::I64],
                variadic: false,
            },
        )
        .expect("seed write extern");
        self.register_extern(
            "exit",
            ExternSig {
                ret: LlvmType::Void,
                args: vec![LlvmType::I32],
                variadic: false,
            },
        )
        .expect("seed exit extern");
    }

    fn collect_user_extern_signatures(&mut self) -> anyhow::Result<()> {
        for function_sig in self.program().function_sigs.values() {
            let Some(symbol) = function_sig.extern_symbol_name.as_ref() else {
                continue;
            };
            let mut args = Vec::new();
            for parameter in &function_sig.parameters {
                args.push(type_ref_to_llvm(&parameter.ty, self.program())?);
            }
            let ret = type_ref_to_llvm(&function_sig.return_type, self.program())?;
            self.register_extern(
                symbol,
                ExternSig {
                    ret,
                    args,
                    variadic: false,
                },
            )?;
        }
        Ok(())
    }

    fn register_extern(&mut self, symbol: &str, sig: ExternSig) -> anyhow::Result<()> {
        if let Some(existing) = self.extern_sigs.get(symbol) {
            if existing.ret != sig.ret
                || existing.args != sig.args
                || existing.variadic != sig.variadic
            {
                bail!("conflicting extern signatures for symbol {symbol}");
            }
            return Ok(());
        }
        self.extern_sigs.insert(symbol.to_string(), sig);
        Ok(())
    }

    fn register_string_literal(&mut self, literal: &str) -> String {
        let mut bytes = literal.as_bytes().to_vec();
        bytes.push(0);
        if let Some(name) = self.string_literal_names.get(&bytes) {
            return name.clone();
        }

        let name = format!("str_lit_{}", self.next_string_literal_id);
        self.next_string_literal_id += 1;
        self.string_literal_names
            .insert(bytes.clone(), name.clone());
        self.string_literal_defs.push((name.clone(), bytes));
        name
    }

    fn emit(self) -> anyhow::Result<String> {
        let program = self.program();

        let mut out = String::new();
        out.push_str("; generated by oac llvm backend\n");
        out.push_str("source_filename = \"oac\"\n\n");

        out.push_str(&format!(
            "@{} = private unnamed_addr constant [4 x i8] c\"%u\\0A\\00\", align 1\n",
            INTEGER_FMT_GLOBAL
        ));
        out.push_str(&format!(
            "@{} = private unnamed_addr constant [2 x i8] c\"\\0A\\00\", align 1\n",
            PRINT_STR_NEWLINE_GLOBAL
        ));

        let mut string_defs = self.string_literal_defs.clone();
        string_defs.sort_by(|a, b| a.0.cmp(&b.0));
        for (name, bytes) in &string_defs {
            out.push_str(&format!(
                "@{} = private unnamed_addr constant [{} x i8] {}, align 1\n",
                name,
                bytes.len(),
                llvm_byte_string_literal(bytes)
            ));
        }
        out.push('\n');

        out.push_str(&emit_builtin_functions(program)?);
        out.push('\n');

        let mut user_functions = self.user_function_texts.clone();
        user_functions.sort();
        for function in user_functions {
            out.push_str(&function);
            out.push('\n');
        }

        let mut defined = builtin_names()
            .into_iter()
            .map(|name| name.to_string())
            .collect::<HashSet<_>>();
        defined.extend(program.function_definitions.keys().cloned());

        let mut extern_symbols = self.extern_sigs.keys().cloned().collect::<Vec<_>>();
        extern_symbols.sort();
        for symbol in extern_symbols {
            if defined.contains(&symbol) {
                continue;
            }
            let sig = self
                .extern_sigs
                .get(&symbol)
                .with_context(|| format!("missing extern signature for {symbol}"))?;
            out.push_str(&emit_extern_decl(&symbol, sig));
            out.push('\n');
        }

        Ok(out)
    }
}

struct FunctionEmitter<'m, 'p> {
    module: &'m mut ModuleEmitter<'p>,
    name: String,
    return_type_ref: String,
    return_llvm_ty: LlvmType,
    body_lines: Vec<String>,
    entry_allocas: Vec<String>,
    vars: HashMap<String, VarSlot>,
    next_reg: u64,
    next_label: u64,
    next_slot: u64,
    terminated: bool,
}

impl<'m, 'p> FunctionEmitter<'m, 'p> {
    fn new(
        module: &'m mut ModuleEmitter<'p>,
        name: &str,
        sig: &FunctionSignature,
    ) -> anyhow::Result<Self> {
        let return_llvm_ty = type_ref_to_llvm(&sig.return_type, module.program())?;
        let mut this = Self {
            module,
            name: name.to_string(),
            return_type_ref: sig.return_type.clone(),
            return_llvm_ty,
            body_lines: Vec::new(),
            entry_allocas: Vec::new(),
            vars: HashMap::new(),
            next_reg: 0,
            next_label: 0,
            next_slot: 0,
            terminated: false,
        };

        for (idx, param) in sig.parameters.iter().enumerate() {
            let arg_name = format!("%arg{idx}");
            let param_llvm_ty = type_ref_to_llvm(&param.ty, this.module.program())?;
            let slot = this.ensure_slot(&param.name, &param.ty)?;
            this.emit_instr(format!(
                "store {} {}, ptr {}, align {}",
                param_llvm_ty.as_ir(),
                arg_name,
                slot.slot,
                param_llvm_ty.align()
            ));
        }

        Ok(this)
    }

    fn sanitize_ident(input: &str) -> String {
        let mut out = String::new();
        for (idx, ch) in input.chars().enumerate() {
            let keep = ch.is_ascii_alphanumeric() || ch == '_';
            if keep {
                if idx == 0 && ch.is_ascii_digit() {
                    out.push('_');
                }
                out.push(ch);
            } else {
                out.push('_');
            }
        }
        if out.is_empty() {
            "sym".to_string()
        } else {
            out
        }
    }

    fn new_reg(&mut self) -> String {
        self.next_reg += 1;
        format!("%r{}", self.next_reg)
    }

    fn new_label(&mut self, prefix: &str) -> String {
        self.next_label += 1;
        format!("{}_{}", Self::sanitize_ident(prefix), self.next_label)
    }

    fn new_slot_name(&mut self, prefix: &str) -> String {
        self.next_slot += 1;
        format!("%slot_{}_{}", Self::sanitize_ident(prefix), self.next_slot)
    }

    fn emit_instr(&mut self, line: impl Into<String>) {
        self.body_lines.push(format!("  {}", line.into()));
    }

    fn begin_block(&mut self, label: &str) {
        self.body_lines.push(format!("{}:", label));
        self.terminated = false;
    }

    fn ensure_reachable_block(&mut self) {
        if self.terminated {
            let label = self.new_label("dead");
            self.begin_block(&label);
        }
    }

    fn emit_branch(&mut self, target_label: &str) {
        self.emit_instr(format!("br label %{}", target_label));
        self.terminated = true;
    }

    fn emit_return(&mut self, value: Option<(LlvmType, String)>) {
        match value {
            Some((ty, repr)) => self.emit_instr(format!("ret {} {}", ty.as_ir(), repr)),
            None => self.emit_instr("ret void"),
        }
        self.terminated = true;
    }

    fn ensure_slot(&mut self, name: &str, type_ref: &str) -> anyhow::Result<VarSlot> {
        if let Some(existing) = self.vars.get(name) {
            if existing.ty != type_ref {
                bail!(
                    "variable {} type mismatch in LLVM lowering: existing {}, new {}",
                    name,
                    existing.ty,
                    type_ref
                );
            }
            return Ok(existing.clone());
        }

        let llvm_ty = type_ref_to_llvm(type_ref, self.module.program())?;
        let slot = self.new_slot_name(name);
        self.entry_allocas.push(format!(
            "  {} = alloca {}, align {}",
            slot,
            llvm_ty.as_ir(),
            llvm_ty.align()
        ));
        let var = VarSlot {
            slot: slot.clone(),
            ty: type_ref.to_string(),
        };
        self.vars.insert(name.to_string(), var.clone());
        Ok(var)
    }

    fn allocate_temp_slot(&mut self, prefix: &str, llvm_ty: LlvmType) -> String {
        let slot = self.new_slot_name(prefix);
        self.entry_allocas.push(format!(
            "  {} = alloca {}, align {}",
            slot,
            llvm_ty.as_ir(),
            llvm_ty.align()
        ));
        slot
    }

    fn cast_value(&mut self, value: &str, from: LlvmType, to: LlvmType) -> anyhow::Result<String> {
        if from == to {
            return Ok(value.to_string());
        }

        let reg = self.new_reg();
        match (from, to) {
            (LlvmType::I32, LlvmType::I64) => {
                self.emit_instr(format!("{} = sext i32 {} to i64", reg, value));
            }
            (LlvmType::I64, LlvmType::I32) => {
                self.emit_instr(format!("{} = trunc i64 {} to i32", reg, value));
            }
            (LlvmType::Float, LlvmType::Double) => {
                self.emit_instr(format!("{} = fpext float {} to double", reg, value));
            }
            (LlvmType::Double, LlvmType::Float) => {
                self.emit_instr(format!("{} = fptrunc double {} to float", reg, value));
            }
            (LlvmType::I32, LlvmType::Float) => {
                self.emit_instr(format!("{} = sitofp i32 {} to float", reg, value));
            }
            (LlvmType::I32, LlvmType::Double) => {
                self.emit_instr(format!("{} = sitofp i32 {} to double", reg, value));
            }
            (LlvmType::I64, LlvmType::Float) => {
                self.emit_instr(format!("{} = sitofp i64 {} to float", reg, value));
            }
            (LlvmType::I64, LlvmType::Double) => {
                self.emit_instr(format!("{} = sitofp i64 {} to double", reg, value));
            }
            (LlvmType::Float, LlvmType::I32) => {
                self.emit_instr(format!("{} = fptosi float {} to i32", reg, value));
            }
            (LlvmType::Float, LlvmType::I64) => {
                self.emit_instr(format!("{} = fptosi float {} to i64", reg, value));
            }
            (LlvmType::Double, LlvmType::I32) => {
                self.emit_instr(format!("{} = fptosi double {} to i32", reg, value));
            }
            (LlvmType::Double, LlvmType::I64) => {
                self.emit_instr(format!("{} = fptosi double {} to i64", reg, value));
            }
            (_, LlvmType::Void) | (LlvmType::Void, _) => {
                bail!("invalid cast involving void from {:?} to {:?}", from, to)
            }
            _ => bail!("unsupported LLVM cast from {:?} to {:?}", from, to),
        }
        Ok(reg)
    }

    fn load_from_slot(&mut self, slot: &VarSlot) -> anyhow::Result<ExprValue> {
        let llvm_ty = type_ref_to_llvm(&slot.ty, self.module.program())?;
        let reg = self.new_reg();
        self.emit_instr(format!(
            "{} = load {}, ptr {}, align {}",
            reg,
            llvm_ty.as_ir(),
            slot.slot,
            llvm_ty.align()
        ));
        Ok(ExprValue {
            ty: slot.ty.clone(),
            llvm_ty,
            repr: reg,
        })
    }

    fn store_to_i64_address(
        &mut self,
        addr_i64: &str,
        llvm_ty: LlvmType,
        value: &str,
    ) -> anyhow::Result<()> {
        let ptr_reg = self.new_reg();
        self.emit_instr(format!("{} = inttoptr i64 {} to ptr", ptr_reg, addr_i64));
        self.emit_instr(format!(
            "store {} {}, ptr {}, align {}",
            llvm_ty.as_ir(),
            value,
            ptr_reg,
            llvm_ty.align()
        ));
        Ok(())
    }

    fn load_from_i64_address(
        &mut self,
        addr_i64: &str,
        llvm_ty: LlvmType,
    ) -> anyhow::Result<String> {
        let ptr_reg = self.new_reg();
        self.emit_instr(format!("{} = inttoptr i64 {} to ptr", ptr_reg, addr_i64));
        let reg = self.new_reg();
        self.emit_instr(format!(
            "{} = load {}, ptr {}, align {}",
            reg,
            llvm_ty.as_ir(),
            ptr_reg,
            llvm_ty.align()
        ));
        Ok(reg)
    }

    fn zero_value(llvm_ty: LlvmType) -> &'static str {
        match llvm_ty {
            LlvmType::I32 | LlvmType::I64 => "0",
            LlvmType::Float | LlvmType::Double => "0.0",
            LlvmType::Void => "0",
        }
    }

    fn to_bool_i1(&mut self, value: &ExprValue) -> anyhow::Result<String> {
        match value.llvm_ty {
            LlvmType::I32 => {
                let reg = self.new_reg();
                self.emit_instr(format!("{} = icmp ne i32 {}, 0", reg, value.repr));
                Ok(reg)
            }
            LlvmType::I64 => {
                let reg = self.new_reg();
                self.emit_instr(format!("{} = icmp ne i64 {}, 0", reg, value.repr));
                Ok(reg)
            }
            LlvmType::Float => {
                let reg = self.new_reg();
                self.emit_instr(format!("{} = fcmp one float {}, 0.0", reg, value.repr));
                Ok(reg)
            }
            LlvmType::Double => {
                let reg = self.new_reg();
                self.emit_instr(format!("{} = fcmp one double {}, 0.0", reg, value.repr));
                Ok(reg)
            }
            LlvmType::Void => bail!("cannot use void expression as condition"),
        }
    }

    fn bool_i1_to_i32(&mut self, i1: &str) -> String {
        let reg = self.new_reg();
        self.emit_instr(format!("{} = zext i1 {} to i32", reg, i1));
        reg
    }

    fn call_symbol(
        &mut self,
        ret_ty: LlvmType,
        symbol: &str,
        args: &[(LlvmType, String)],
    ) -> String {
        let rendered_args = args
            .iter()
            .map(|(ty, repr)| format!("{} {}", ty.as_ir(), repr))
            .collect::<Vec<_>>()
            .join(", ");

        if ret_ty == LlvmType::Void {
            self.emit_instr(format!("call void @{}({})", symbol, rendered_args));
            return String::new();
        }

        let result = self.new_reg();
        self.emit_instr(format!(
            "{} = call {} @{}({})",
            result,
            ret_ty.as_ir(),
            symbol,
            rendered_args
        ));
        result
    }

    fn maybe_clone_struct_value(&mut self, value: ExprValue) -> anyhow::Result<ExprValue> {
        if !is_struct_type(self.module.program(), &value.ty) {
            return Ok(value);
        }

        let size = runtime_layout::struct_size_bytes_by_name(self.module.program(), &value.ty);
        let alloc_size = non_zero_allocation_size(size);
        let cloned = self.call_symbol(
            LlvmType::I64,
            "calloc",
            &[
                (LlvmType::I64, "1".to_string()),
                (LlvmType::I64, alloc_size.to_string()),
            ],
        );
        let _ = self.call_symbol(
            LlvmType::I64,
            "memcpy",
            &[
                (LlvmType::I64, cloned.clone()),
                (LlvmType::I64, value.repr),
                (LlvmType::I64, size.to_string()),
            ],
        );

        Ok(ExprValue {
            ty: value.ty,
            llvm_ty: LlvmType::I64,
            repr: cloned,
        })
    }

    fn compile_named_call(
        &mut self,
        function_name: &str,
        args: &[parser::Expression],
    ) -> anyhow::Result<ExprValue> {
        let sig = self
            .module
            .program()
            .function_sigs
            .get(function_name)
            .with_context(|| format!("unknown function {} in LLVM lowering", function_name))?
            .clone();

        if args.len() != sig.parameters.len() {
            bail!(
                "function {} argument count mismatch in LLVM lowering: expected {}, got {}",
                function_name,
                sig.parameters.len(),
                args.len()
            );
        }

        let mut lowered_args = Vec::new();
        for (idx, arg_expr) in args.iter().enumerate() {
            let mut arg = self.compile_expr(arg_expr)?;
            if is_struct_type(self.module.program(), &arg.ty) {
                arg = self.maybe_clone_struct_value(arg)?;
            }
            let expected_ty_ref = &sig.parameters[idx].ty;
            let expected_llvm_ty = type_ref_to_llvm(expected_ty_ref, self.module.program())?;
            let arg_repr = self.cast_value(&arg.repr, arg.llvm_ty, expected_llvm_ty)?;
            lowered_args.push((expected_llvm_ty, arg_repr));
        }

        let call_symbol = call_target_symbol(function_name, &sig);
        let ret_llvm_ty = type_ref_to_llvm(&sig.return_type, self.module.program())?;
        if ret_llvm_ty == LlvmType::Void {
            bail!(
                "void-return call {} cannot be used as expression value",
                function_name
            );
        }

        let repr = self.call_symbol(ret_llvm_ty, &call_symbol, &lowered_args);
        Ok(ExprValue {
            ty: sig.return_type,
            llvm_ty: ret_llvm_ty,
            repr,
        })
    }

    fn compile_void_call_statement(&mut self, expr: &parser::Expression) -> anyhow::Result<bool> {
        let Some((function_name, args)) = resolve_void_call_target(self.module.program(), expr)
        else {
            return Ok(false);
        };

        let sig = self
            .module
            .program()
            .function_sigs
            .get(&function_name)
            .with_context(|| format!("unknown void call target {}", function_name))?
            .clone();

        let mut lowered_args = Vec::new();
        for (idx, arg_expr) in args.iter().enumerate() {
            let mut arg = self.compile_expr(arg_expr)?;
            if is_struct_type(self.module.program(), &arg.ty) {
                arg = self.maybe_clone_struct_value(arg)?;
            }
            let expected_ty_ref = &sig.parameters[idx].ty;
            let expected_llvm_ty = type_ref_to_llvm(expected_ty_ref, self.module.program())?;
            let arg_repr = self.cast_value(&arg.repr, arg.llvm_ty, expected_llvm_ty)?;
            lowered_args.push((expected_llvm_ty, arg_repr));
        }

        let symbol = call_target_symbol(&function_name, &sig);
        let _ = self.call_symbol(LlvmType::Void, &symbol, &lowered_args);
        Ok(true)
    }

    fn compile_statement(&mut self, statement: &parser::Statement) -> anyhow::Result<()> {
        match statement {
            parser::Statement::StructDef { .. } => Ok(()),
            parser::Statement::Prove { .. } => Ok(()),
            parser::Statement::Assign { variable, value } => {
                let mut value_expr = self.compile_expr(value)?;
                if let Some(existing) = self.vars.get(variable).cloned() {
                    value_expr = if is_struct_type(self.module.program(), &existing.ty) {
                        self.maybe_clone_struct_value(value_expr)?
                    } else {
                        value_expr
                    };
                    let llvm_ty = type_ref_to_llvm(&existing.ty, self.module.program())?;
                    let casted = self.cast_value(&value_expr.repr, value_expr.llvm_ty, llvm_ty)?;
                    self.emit_instr(format!(
                        "store {} {}, ptr {}, align {}",
                        llvm_ty.as_ir(),
                        casted,
                        existing.slot,
                        llvm_ty.align()
                    ));
                    return Ok(());
                }

                value_expr = if is_struct_type(self.module.program(), &value_expr.ty) {
                    self.maybe_clone_struct_value(value_expr)?
                } else {
                    value_expr
                };

                let slot = self.ensure_slot(variable, &value_expr.ty)?;
                let llvm_ty = type_ref_to_llvm(&slot.ty, self.module.program())?;
                let casted = self.cast_value(&value_expr.repr, value_expr.llvm_ty, llvm_ty)?;
                self.emit_instr(format!(
                    "store {} {}, ptr {}, align {}",
                    llvm_ty.as_ir(),
                    casted,
                    slot.slot,
                    llvm_ty.align()
                ));
                Ok(())
            }
            parser::Statement::Return { expr } => {
                let mut result = self.compile_expr(expr)?;
                if is_struct_type(self.module.program(), &result.ty) {
                    result = self.maybe_clone_struct_value(result)?;
                }
                let casted = self.cast_value(&result.repr, result.llvm_ty, self.return_llvm_ty)?;
                self.emit_return(Some((self.return_llvm_ty, casted)));
                Ok(())
            }
            parser::Statement::Expression { expr } => {
                if self.compile_void_call_statement(expr)? {
                    return Ok(());
                }
                let _ = self.compile_expr(expr)?;
                Ok(())
            }
            parser::Statement::Conditional {
                condition,
                body,
                else_body,
            } => self.compile_conditional_statement(condition, body, else_body.as_deref()),
            parser::Statement::While { condition, body } => {
                self.compile_while_statement(condition, body)
            }
            parser::Statement::Assert { condition } => self.compile_assert_statement(condition),
            parser::Statement::Match { subject, arms } => {
                self.compile_match_statement(subject, arms)
            }
        }
    }

    fn compile_conditional_statement(
        &mut self,
        condition: &parser::Expression,
        body: &[parser::Statement],
        else_body: Option<&[parser::Statement]>,
    ) -> anyhow::Result<()> {
        let cond = self.compile_expr(condition)?;
        let cond_i1 = self.to_bool_i1(&cond)?;

        let then_label = self.new_label("cond_then");
        let else_label = self.new_label("cond_else");
        let end_label = self.new_label("cond_end");

        let false_label = if else_body.is_some() {
            else_label.as_str()
        } else {
            end_label.as_str()
        };
        self.emit_instr(format!(
            "br i1 {}, label %{}, label %{}",
            cond_i1, then_label, false_label
        ));
        self.terminated = true;

        self.begin_block(&then_label);
        for stmt in body {
            self.ensure_reachable_block();
            self.compile_statement(stmt)?;
        }
        let then_falls = !self.terminated;
        if then_falls {
            self.emit_branch(&end_label);
        }

        let mut else_falls = false;
        if let Some(else_body) = else_body {
            self.begin_block(&else_label);
            for stmt in else_body {
                self.ensure_reachable_block();
                self.compile_statement(stmt)?;
            }
            else_falls = !self.terminated;
            if else_falls {
                self.emit_branch(&end_label);
            }
        }

        let needs_end = else_body.is_none() || then_falls || else_falls;
        if needs_end {
            self.begin_block(&end_label);
        }
        Ok(())
    }

    fn compile_while_statement(
        &mut self,
        condition: &parser::Expression,
        body: &[parser::Statement],
    ) -> anyhow::Result<()> {
        let cond_label = self.new_label("while_cond");
        let body_label = self.new_label("while_body");
        let end_label = self.new_label("while_end");

        self.emit_branch(&cond_label);

        self.begin_block(&cond_label);
        let cond = self.compile_expr(condition)?;
        let cond_i1 = self.to_bool_i1(&cond)?;
        self.emit_instr(format!(
            "br i1 {}, label %{}, label %{}",
            cond_i1, body_label, end_label
        ));
        self.terminated = true;

        self.begin_block(&body_label);
        for stmt in body {
            self.ensure_reachable_block();
            self.compile_statement(stmt)?;
        }
        if !self.terminated {
            self.emit_branch(&cond_label);
        }

        self.begin_block(&end_label);
        Ok(())
    }

    fn compile_assert_statement(&mut self, condition: &parser::Expression) -> anyhow::Result<()> {
        let cond = self.compile_expr(condition)?;
        let cond_i1 = self.to_bool_i1(&cond)?;

        let pass_label = self.new_label("assert_pass");
        let fail_label = self.new_label("assert_fail");

        self.emit_instr(format!(
            "br i1 {}, label %{}, label %{}",
            cond_i1, pass_label, fail_label
        ));
        self.terminated = true;

        self.begin_block(&fail_label);
        let _ = self.call_symbol(
            LlvmType::Void,
            "exit",
            &[(LlvmType::I32, ASSERT_FAILURE_EXIT_CODE.to_string())],
        );
        self.emit_instr("unreachable");
        self.terminated = true;

        self.begin_block(&pass_label);
        Ok(())
    }

    fn compile_match_statement(
        &mut self,
        subject_expr: &parser::Expression,
        arms: &[parser::MatchArm],
    ) -> anyhow::Result<()> {
        let (subject_var, subject_ty, enum_def, tag_var) =
            self.compile_match_subject(subject_expr, "match")?;
        let end_label = self.new_label("match_end");
        let mut any_fallthrough = false;

        for (idx, arm) in arms.iter().enumerate() {
            let arm_label = self.new_label("match_arm");
            let next_label = if idx + 1 < arms.len() {
                Some(self.new_label("match_next"))
            } else {
                None
            };

            let (variant, binder) = resolve_match_pattern(&enum_def, &subject_ty, &arm.pattern)?;
            let cmp = self.new_reg();
            self.emit_instr(format!(
                "{} = icmp eq i32 {}, {}",
                cmp, tag_var.repr, variant.tag
            ));
            let else_label = next_label.as_ref().unwrap_or(&arm_label);
            self.emit_instr(format!(
                "br i1 {}, label %{}, label %{}",
                cmp, arm_label, else_label
            ));
            self.terminated = true;

            self.begin_block(&arm_label);
            let saved_vars = self.vars.clone();
            self.bind_match_payload(&subject_var, &enum_def, variant, binder.as_deref(), "match")?;
            for stmt in &arm.body {
                self.ensure_reachable_block();
                self.compile_statement(stmt)?;
            }
            let arm_terminated = self.terminated;
            self.vars = saved_vars;
            if !arm_terminated {
                any_fallthrough = true;
                self.emit_branch(&end_label);
            }

            if let Some(next_label) = next_label {
                self.begin_block(&next_label);
            }
        }

        if any_fallthrough {
            self.begin_block(&end_label);
        }

        Ok(())
    }

    fn compile_match_expression(
        &mut self,
        subject_expr: &parser::Expression,
        arms: &[parser::MatchExprArm],
    ) -> anyhow::Result<ExprValue> {
        let var_types = self
            .vars
            .iter()
            .map(|(name, slot)| (name.clone(), slot.ty.clone()))
            .collect::<HashMap<_, _>>();
        let match_ty = ir::get_expression_type(
            &parser::Expression::Match {
                subject: Box::new(subject_expr.clone()),
                arms: arms.to_vec(),
            },
            &var_types,
            &self.module.program().function_sigs,
            &self.module.program().type_definitions,
            &self.module.program().trait_method_signatures,
            &self.module.program().trait_impl_methods,
        )
        .context("failed to type-check match expression in LLVM lowering")?;
        let match_llvm_ty = type_ref_to_llvm(&match_ty, self.module.program())?;

        let result_slot = self.allocate_temp_slot("match_expr", match_llvm_ty);
        let (subject_var, subject_ty, enum_def, tag_var) =
            self.compile_match_subject(subject_expr, "match_expr")?;
        let end_label = self.new_label("match_expr_end");

        for (idx, arm) in arms.iter().enumerate() {
            let arm_label = self.new_label("match_expr_arm");
            let next_label = if idx + 1 < arms.len() {
                Some(self.new_label("match_expr_next"))
            } else {
                None
            };

            let (variant, binder) = resolve_match_pattern(&enum_def, &subject_ty, &arm.pattern)?;
            let cmp = self.new_reg();
            self.emit_instr(format!(
                "{} = icmp eq i32 {}, {}",
                cmp, tag_var.repr, variant.tag
            ));
            let else_label = next_label.as_ref().unwrap_or(&arm_label);
            self.emit_instr(format!(
                "br i1 {}, label %{}, label %{}",
                cmp, arm_label, else_label
            ));
            self.terminated = true;

            self.begin_block(&arm_label);
            let saved_vars = self.vars.clone();
            self.bind_match_payload(
                &subject_var,
                &enum_def,
                variant,
                binder.as_deref(),
                "match_expr",
            )?;
            let arm_value = self.compile_expr(&arm.value)?;
            let casted = self.cast_value(&arm_value.repr, arm_value.llvm_ty, match_llvm_ty)?;
            self.emit_instr(format!(
                "store {} {}, ptr {}, align {}",
                match_llvm_ty.as_ir(),
                casted,
                result_slot,
                match_llvm_ty.align()
            ));
            self.vars = saved_vars;
            self.emit_branch(&end_label);

            if let Some(next_label) = next_label {
                self.begin_block(&next_label);
            }
        }

        self.begin_block(&end_label);
        let loaded = self.new_reg();
        self.emit_instr(format!(
            "{} = load {}, ptr {}, align {}",
            loaded,
            match_llvm_ty.as_ir(),
            result_slot,
            match_llvm_ty.align()
        ));

        Ok(ExprValue {
            ty: match_ty,
            llvm_ty: match_llvm_ty,
            repr: loaded,
        })
    }

    fn compile_match_subject(
        &mut self,
        subject_expr: &parser::Expression,
        label_root: &str,
    ) -> anyhow::Result<(ExprValue, String, ir::EnumTypeDef, ExprValue)> {
        let subject = self.compile_expr(subject_expr)?;
        let subject_ty = subject.ty.clone();
        let enum_def = match self.module.program().type_definitions.get(&subject.ty) {
            Some(TypeDef::Enum(enum_def)) => enum_def.clone(),
            _ => bail!("match subject must be enum, got {}", subject.ty),
        };

        let tag_value = if enum_def.is_tagged_union {
            let tag_addr = self.new_reg();
            self.emit_instr(format!("{} = add i64 {}, 0", tag_addr, subject.repr));
            let tag_repr = self.load_from_i64_address(&tag_addr, LlvmType::I32)?;
            ExprValue {
                ty: "I32".to_string(),
                llvm_ty: LlvmType::I32,
                repr: tag_repr,
            }
        } else {
            let tag_repr = self.cast_value(&subject.repr, subject.llvm_ty, LlvmType::I32)?;
            ExprValue {
                ty: "I32".to_string(),
                llvm_ty: LlvmType::I32,
                repr: tag_repr,
            }
        };

        let _ = label_root;
        Ok((subject, subject_ty, enum_def, tag_value))
    }

    fn bind_match_payload(
        &mut self,
        subject: &ExprValue,
        enum_def: &ir::EnumTypeDef,
        variant: &ir::EnumVariant,
        binder: Option<&str>,
        label_root: &str,
    ) -> anyhow::Result<()> {
        let _ = enum_def;
        if let (Some(binder), Some(payload_ty)) = (binder, variant.payload_ty.clone()) {
            let payload_llvm_ty = type_ref_to_llvm(&payload_ty, self.module.program())?;
            let payload_addr = self.new_reg();
            self.emit_instr(format!(
                "{} = add i64 {}, {}",
                payload_addr,
                subject.repr,
                runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
            ));
            let payload_value = self.load_from_i64_address(&payload_addr, payload_llvm_ty)?;
            let slot = self.ensure_slot(binder, &payload_ty)?;
            self.emit_instr(format!(
                "store {} {}, ptr {}, align {}",
                payload_llvm_ty.as_ir(),
                payload_value,
                slot.slot,
                payload_llvm_ty.align()
            ));
            let _ = label_root;
        }
        Ok(())
    }

    fn compile_postfix_call(
        &mut self,
        callee: &parser::Expression,
        args: &[parser::Expression],
    ) -> anyhow::Result<ExprValue> {
        let parser::Expression::FieldAccess {
            struct_variable,
            field,
        } = callee
        else {
            bail!("unsupported postfix call target");
        };

        if let Some(TypeDef::Enum(enum_def)) = self
            .module
            .program()
            .type_definitions
            .get(struct_variable)
            .cloned()
        {
            if let Some(variant) = enum_def.variants.iter().find(|v| v.name == *field) {
                let payload_ty = variant
                    .payload_ty
                    .as_ref()
                    .with_context(|| format!("tag-only enum variant {} is not callable", field))?
                    .clone();
                if args.len() != 1 {
                    bail!(
                        "enum payload constructors currently support one argument, got {}",
                        args.len()
                    );
                }
                let arg = self.compile_expr(&args[0])?;
                let payload_llvm_ty = type_ref_to_llvm(&payload_ty, self.module.program())?;
                let payload_repr = self.cast_value(&arg.repr, arg.llvm_ty, payload_llvm_ty)?;

                let enum_ptr = self.call_symbol(
                    LlvmType::I64,
                    "malloc",
                    &[(
                        LlvmType::I64,
                        runtime_layout::TAGGED_UNION_SIZE_BYTES.to_string(),
                    )],
                );
                self.store_to_i64_address(&enum_ptr, LlvmType::I32, &variant.tag.to_string())?;

                let payload_addr = self.new_reg();
                self.emit_instr(format!(
                    "{} = add i64 {}, {}",
                    payload_addr,
                    enum_ptr,
                    runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
                ));
                self.store_to_i64_address(&payload_addr, payload_llvm_ty, &payload_repr)?;

                return Ok(ExprValue {
                    ty: enum_def.name.clone(),
                    llvm_ty: LlvmType::I64,
                    repr: enum_ptr,
                });
            }
        }

        if self
            .module
            .program()
            .trait_method_signatures
            .contains_key(&trait_method_key(struct_variable, field))
        {
            if args.is_empty() {
                bail!(
                    "trait call {}.{} must pass receiver argument",
                    struct_variable,
                    field
                );
            }
            let var_types = self
                .vars
                .iter()
                .map(|(name, slot)| (name.clone(), slot.ty.clone()))
                .collect::<HashMap<_, _>>();
            let self_type = ir::get_expression_type(
                &args[0],
                &var_types,
                &self.module.program().function_sigs,
                &self.module.program().type_definitions,
                &self.module.program().trait_method_signatures,
                &self.module.program().trait_impl_methods,
            )
            .context("failed to resolve trait call receiver type")?;
            let impl_key = trait_impl_method_key(struct_variable, &self_type, field);
            let target = self
                .module
                .program()
                .trait_impl_methods
                .get(&impl_key)
                .with_context(|| {
                    format!(
                        "missing impl for trait call {}.{} with receiver type {}",
                        struct_variable, field, self_type
                    )
                })?
                .clone();
            return self.compile_named_call(&target, args);
        }

        let namespaced_call = parser::qualify_namespace_function_name(struct_variable, field);
        if self
            .module
            .program()
            .function_sigs
            .contains_key(&namespaced_call)
        {
            return self.compile_named_call(&namespaced_call, args);
        }

        bail!("unsupported postfix call target")
    }

    fn compile_expr(&mut self, expr: &parser::Expression) -> anyhow::Result<ExprValue> {
        match expr {
            parser::Expression::Match { subject, arms } => {
                self.compile_match_expression(subject, arms)
            }
            parser::Expression::Literal(parser::Literal::Int(value)) => Ok(ExprValue {
                ty: "I32".to_string(),
                llvm_ty: LlvmType::I32,
                repr: value.to_string(),
            }),
            parser::Expression::Literal(parser::Literal::Float32(value)) => Ok(ExprValue {
                ty: "FP32".to_string(),
                llvm_ty: LlvmType::Float,
                repr: value.clone(),
            }),
            parser::Expression::Literal(parser::Literal::Float64(value)) => Ok(ExprValue {
                ty: "FP64".to_string(),
                llvm_ty: LlvmType::Double,
                repr: value.clone(),
            }),
            parser::Expression::Literal(parser::Literal::Bool(value)) => Ok(ExprValue {
                ty: "Bool".to_string(),
                llvm_ty: LlvmType::I32,
                repr: if *value {
                    "1".to_string()
                } else {
                    "0".to_string()
                },
            }),
            parser::Expression::Literal(parser::Literal::String(value)) => {
                let global = self.module.register_string_literal(value);
                let literal_ptr = self.new_reg();
                self.emit_instr(format!("{} = ptrtoint ptr @{} to i64", literal_ptr, global));

                let bytes_struct = runtime_layout::std_bytes_struct(self.module.program());
                let bytes_ptr_offset = runtime_layout::struct_field_offset(
                    self.module.program(),
                    &bytes_struct,
                    "ptr",
                );
                let bytes_len_offset = runtime_layout::struct_field_offset(
                    self.module.program(),
                    &bytes_struct,
                    "len",
                );
                let bytes_size =
                    runtime_layout::struct_size_bytes(self.module.program(), &bytes_struct);
                let string_enum = runtime_layout::std_string_enum(self.module.program());
                let literal_tag = runtime_layout::enum_variant_tag(&string_enum, "Literal");

                let bytes_ptr = self.call_symbol(
                    LlvmType::I64,
                    "malloc",
                    &[(LlvmType::I64, bytes_size.to_string())],
                );

                let bytes_ptr_addr = self.new_reg();
                self.emit_instr(format!(
                    "{} = add i64 {}, {}",
                    bytes_ptr_addr, bytes_ptr, bytes_ptr_offset
                ));
                self.store_to_i64_address(&bytes_ptr_addr, LlvmType::I64, &literal_ptr)?;

                let bytes_len_addr = self.new_reg();
                self.emit_instr(format!(
                    "{} = add i64 {}, {}",
                    bytes_len_addr, bytes_ptr, bytes_len_offset
                ));
                self.store_to_i64_address(
                    &bytes_len_addr,
                    LlvmType::I32,
                    &value.len().to_string(),
                )?;

                let string_ptr = self.call_symbol(
                    LlvmType::I64,
                    "malloc",
                    &[(
                        LlvmType::I64,
                        runtime_layout::TAGGED_UNION_SIZE_BYTES.to_string(),
                    )],
                );
                self.store_to_i64_address(&string_ptr, LlvmType::I32, &literal_tag.to_string())?;

                let payload_addr = self.new_reg();
                self.emit_instr(format!(
                    "{} = add i64 {}, {}",
                    payload_addr,
                    string_ptr,
                    runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
                ));
                self.store_to_i64_address(&payload_addr, LlvmType::I64, &bytes_ptr)?;

                Ok(ExprValue {
                    ty: "String".to_string(),
                    llvm_ty: LlvmType::I64,
                    repr: string_ptr,
                })
            }
            parser::Expression::Variable(name) => {
                let slot = self
                    .vars
                    .get(name)
                    .with_context(|| format!("unknown variable {} in LLVM lowering", name))?
                    .clone();
                self.load_from_slot(&slot)
            }
            parser::Expression::UnaryOp(op, inner) => {
                let value = self.compile_expr(inner)?;
                match op {
                    UnaryOp::Not => {
                        let i1 = self.to_bool_i1(&value)?;
                        let reg = self.new_reg();
                        self.emit_instr(format!("{} = xor i1 {}, true", reg, i1));
                        let as_i32 = self.bool_i1_to_i32(&reg);
                        Ok(ExprValue {
                            ty: "Bool".to_string(),
                            llvm_ty: LlvmType::I32,
                            repr: as_i32,
                        })
                    }
                }
            }
            parser::Expression::Call(name, args) => self.compile_named_call(name, args),
            parser::Expression::PostfixCall { callee, args } => {
                self.compile_postfix_call(callee, args)
            }
            parser::Expression::FieldAccess {
                struct_variable,
                field,
            } => {
                if let Some(slot) = self.vars.get(struct_variable).cloned() {
                    let struct_ptr = self.load_from_slot(&slot)?;
                    let type_def = self
                        .module
                        .program()
                        .type_definitions
                        .get(&slot.ty)
                        .with_context(|| format!("unknown field-access type {}", slot.ty))?;
                    let TypeDef::Struct(struct_def) = type_def else {
                        bail!("field access on non-struct variable {}", struct_variable);
                    };
                    let field_info = struct_def
                        .struct_fields
                        .iter()
                        .find(|item| item.name == *field)
                        .with_context(|| {
                            format!("unknown field {} on struct {}", field, struct_def.name)
                        })?;
                    let field_llvm_ty = type_ref_to_llvm(&field_info.ty, self.module.program())?;
                    let field_offset = runtime_layout::struct_field_offset(
                        self.module.program(),
                        struct_def,
                        field,
                    );
                    let field_addr = self.new_reg();
                    self.emit_instr(format!(
                        "{} = add i64 {}, {}",
                        field_addr, struct_ptr.repr, field_offset
                    ));
                    let field_value = self.load_from_i64_address(&field_addr, field_llvm_ty)?;
                    return Ok(ExprValue {
                        ty: field_info.ty.clone(),
                        llvm_ty: field_llvm_ty,
                        repr: field_value,
                    });
                }

                let enum_def = match self
                    .module
                    .program()
                    .type_definitions
                    .get(struct_variable)
                    .with_context(|| {
                        format!("unknown variable/type {} in field access", struct_variable)
                    })? {
                    TypeDef::Enum(enum_def) => enum_def,
                    _ => bail!("unknown variable/type {}", struct_variable),
                };
                let variant = enum_def
                    .variants
                    .iter()
                    .find(|variant| variant.name == *field)
                    .with_context(|| {
                        format!(
                            "unknown enum variant {}.{} in field access",
                            struct_variable, field
                        )
                    })?;
                if variant.payload_ty.is_some() {
                    bail!("payload enum variant requires constructor call");
                }

                if enum_def.is_tagged_union {
                    let enum_ptr = self.call_symbol(
                        LlvmType::I64,
                        "malloc",
                        &[(
                            LlvmType::I64,
                            runtime_layout::TAGGED_UNION_SIZE_BYTES.to_string(),
                        )],
                    );
                    self.store_to_i64_address(&enum_ptr, LlvmType::I32, &variant.tag.to_string())?;
                    let payload_addr = self.new_reg();
                    self.emit_instr(format!(
                        "{} = add i64 {}, {}",
                        payload_addr,
                        enum_ptr,
                        runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
                    ));
                    self.store_to_i64_address(&payload_addr, LlvmType::I64, "0")?;
                    Ok(ExprValue {
                        ty: enum_def.name.clone(),
                        llvm_ty: LlvmType::I64,
                        repr: enum_ptr,
                    })
                } else {
                    Ok(ExprValue {
                        ty: enum_def.name.clone(),
                        llvm_ty: LlvmType::I32,
                        repr: variant.tag.to_string(),
                    })
                }
            }
            parser::Expression::StructValue {
                struct_name,
                field_values,
            } => {
                let type_def = self
                    .module
                    .program()
                    .type_definitions
                    .get(struct_name)
                    .with_context(|| format!("unknown struct type {}", struct_name))?;
                let TypeDef::Struct(struct_def) = type_def else {
                    bail!("{} is not a struct", struct_name);
                };

                let struct_size =
                    runtime_layout::struct_size_bytes(self.module.program(), struct_def);
                let struct_ptr = self.call_symbol(
                    LlvmType::I64,
                    "calloc",
                    &[
                        (LlvmType::I64, "1".to_string()),
                        (
                            LlvmType::I64,
                            non_zero_allocation_size(struct_size).to_string(),
                        ),
                    ],
                );

                for (field_name, field_value_expr) in field_values {
                    let field_value = self.compile_expr(field_value_expr)?;
                    let field = struct_def
                        .struct_fields
                        .iter()
                        .find(|item| item.name == *field_name)
                        .with_context(|| {
                            format!("unknown struct field {}.{}", struct_name, field_name)
                        })?;
                    let field_llvm_ty = type_ref_to_llvm(&field.ty, self.module.program())?;
                    let field_offset = runtime_layout::struct_field_offset(
                        self.module.program(),
                        struct_def,
                        field_name,
                    );
                    let casted =
                        self.cast_value(&field_value.repr, field_value.llvm_ty, field_llvm_ty)?;
                    let field_addr = self.new_reg();
                    self.emit_instr(format!(
                        "{} = add i64 {}, {}",
                        field_addr, struct_ptr, field_offset
                    ));
                    self.store_to_i64_address(&field_addr, field_llvm_ty, &casted)?;
                }

                Ok(ExprValue {
                    ty: struct_name.to_string(),
                    llvm_ty: LlvmType::I64,
                    repr: struct_ptr,
                })
            }
            parser::Expression::BinOp(op, left, right) => {
                let left_value = self.compile_expr(left)?;
                let right_value = self.compile_expr(right)?;

                if matches!(op, Op::Eq | Op::Neq)
                    && is_struct_type(self.module.program(), &left_value.ty)
                {
                    let size = runtime_layout::struct_size_bytes_by_name(
                        self.module.program(),
                        &left_value.ty,
                    );
                    let memcmp_result = self.call_symbol(
                        LlvmType::I32,
                        "memcmp",
                        &[
                            (LlvmType::I64, left_value.repr),
                            (LlvmType::I64, right_value.repr),
                            (LlvmType::I64, size.to_string()),
                        ],
                    );
                    let cmp_i1 = self.new_reg();
                    let pred = if matches!(op, Op::Eq) { "eq" } else { "ne" };
                    self.emit_instr(format!(
                        "{} = icmp {} i32 {}, 0",
                        cmp_i1, pred, memcmp_result
                    ));
                    let as_i32 = self.bool_i1_to_i32(&cmp_i1);
                    return Ok(ExprValue {
                        ty: "Bool".to_string(),
                        llvm_ty: LlvmType::I32,
                        repr: as_i32,
                    });
                }

                let operand_ty = left_value.llvm_ty;
                let left_repr =
                    self.cast_value(&left_value.repr, left_value.llvm_ty, operand_ty)?;
                let right_repr =
                    self.cast_value(&right_value.repr, right_value.llvm_ty, operand_ty)?;

                let use_unsigned_int_cmp = left_value.ty == "U8";
                let use_ordered_float_cmp = operand_ty.is_float();

                match op {
                    Op::Eq | Op::Neq | Op::Lt | Op::Gt | Op::Le | Op::Ge => {
                        let cmp_i1 = self.new_reg();
                        if use_ordered_float_cmp {
                            let pred = match op {
                                Op::Eq => "oeq",
                                Op::Neq => "one",
                                Op::Lt => "olt",
                                Op::Gt => "ogt",
                                Op::Le => "ole",
                                Op::Ge => "oge",
                                _ => unreachable!(),
                            };
                            self.emit_instr(format!(
                                "{} = fcmp {} {} {}, {}",
                                cmp_i1,
                                pred,
                                operand_ty.as_ir(),
                                left_repr,
                                right_repr
                            ));
                        } else {
                            let pred = match op {
                                Op::Eq => "eq",
                                Op::Neq => "ne",
                                Op::Lt if use_unsigned_int_cmp => "ult",
                                Op::Gt if use_unsigned_int_cmp => "ugt",
                                Op::Le if use_unsigned_int_cmp => "ule",
                                Op::Ge if use_unsigned_int_cmp => "uge",
                                Op::Lt => "slt",
                                Op::Gt => "sgt",
                                Op::Le => "sle",
                                Op::Ge => "sge",
                                _ => unreachable!(),
                            };
                            self.emit_instr(format!(
                                "{} = icmp {} {} {}, {}",
                                cmp_i1,
                                pred,
                                operand_ty.as_ir(),
                                left_repr,
                                right_repr
                            ));
                        }
                        let as_i32 = self.bool_i1_to_i32(&cmp_i1);
                        Ok(ExprValue {
                            ty: "Bool".to_string(),
                            llvm_ty: LlvmType::I32,
                            repr: as_i32,
                        })
                    }
                    Op::Add | Op::Sub | Op::Mul | Op::Div | Op::And | Op::Or => {
                        let op_name = match op {
                            Op::Add if operand_ty.is_float() => "fadd",
                            Op::Sub if operand_ty.is_float() => "fsub",
                            Op::Mul if operand_ty.is_float() => "fmul",
                            Op::Div if operand_ty.is_float() => "fdiv",
                            Op::Div if use_unsigned_int_cmp => "udiv",
                            Op::Add => "add",
                            Op::Sub => "sub",
                            Op::Mul => "mul",
                            Op::Div => "sdiv",
                            Op::And => "and",
                            Op::Or => "or",
                            _ => unreachable!(),
                        };
                        let reg = self.new_reg();
                        self.emit_instr(format!(
                            "{} = {} {} {}, {}",
                            reg,
                            op_name,
                            operand_ty.as_ir(),
                            left_repr,
                            right_repr
                        ));

                        let out_ty = match op {
                            Op::And | Op::Or => "Bool".to_string(),
                            _ => left_value.ty,
                        };
                        Ok(ExprValue {
                            ty: out_ty,
                            llvm_ty: operand_ty,
                            repr: reg,
                        })
                    }
                }
            }
        }
    }

    fn compile_function_body(&mut self, body: &[parser::Statement]) -> anyhow::Result<()> {
        for statement in body {
            self.ensure_reachable_block();
            self.compile_statement(statement)?;
        }
        Ok(())
    }

    fn finalize(mut self, sig: &FunctionSignature) -> anyhow::Result<String> {
        if !self.terminated {
            if self.return_llvm_ty == LlvmType::Void {
                self.emit_return(None);
            } else {
                self.emit_return(Some((
                    self.return_llvm_ty,
                    Self::zero_value(self.return_llvm_ty).to_string(),
                )));
            }
        }

        let args = sig
            .parameters
            .iter()
            .enumerate()
            .map(|(idx, param)| {
                let ty = type_ref_to_llvm(&param.ty, self.module.program())?;
                Ok(format!("{} %arg{}", ty.as_ir(), idx))
            })
            .collect::<anyhow::Result<Vec<_>>>()?
            .join(", ");

        let mut out = String::new();
        out.push_str(&format!(
            "define {} @{}({}) {{\n",
            self.return_llvm_ty.as_ir(),
            self.name,
            args
        ));
        out.push_str("entry:\n");
        for alloca in &self.entry_allocas {
            out.push_str(alloca);
            out.push('\n');
        }
        for line in &self.body_lines {
            out.push_str(line);
            out.push('\n');
        }
        out.push_str("}\n");
        let _ = &self.return_type_ref;
        Ok(out)
    }
}

pub(crate) fn compile(program: &ResolvedProgram) -> anyhow::Result<String> {
    let mut module = ModuleEmitter::new(program)?;

    let mut function_names = program
        .function_definitions
        .keys()
        .cloned()
        .collect::<Vec<_>>();
    function_names.sort();

    for function_name in function_names {
        let function = program
            .function_definitions
            .get(&function_name)
            .with_context(|| format!("missing function definition for {}", function_name))?
            .clone();
        let sig = program
            .function_sigs
            .get(&function_name)
            .with_context(|| format!("missing function signature for {}", function_name))?
            .clone();

        let mut emitter = FunctionEmitter::new(&mut module, &function_name, &sig)?;
        emitter.compile_function_body(&function.body)?;
        let function_text = emitter.finalize(&sig)?;
        module.user_function_texts.push(function_text);
    }

    module.emit()
}

fn non_zero_allocation_size(size: u64) -> u64 {
    if size == 0 {
        1
    } else {
        size
    }
}

fn resolve_void_call_target<'a>(
    program: &ResolvedProgram,
    expr: &'a parser::Expression,
) -> Option<(String, &'a [parser::Expression])> {
    match expr {
        parser::Expression::Call(function_name, args) => {
            let sig = program.function_sigs.get(function_name)?;
            if sig.return_type == "Void" {
                Some((function_name.clone(), args.as_slice()))
            } else {
                None
            }
        }
        parser::Expression::PostfixCall { callee, args } => {
            let parser::Expression::FieldAccess {
                struct_variable,
                field,
            } = callee.as_ref()
            else {
                return None;
            };
            let namespaced_call = parser::qualify_namespace_function_name(struct_variable, field);
            let sig = program.function_sigs.get(&namespaced_call)?;
            if sig.return_type == "Void" {
                Some((namespaced_call, args.as_slice()))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn call_target_symbol(function_name: &str, sig: &FunctionSignature) -> String {
    sig.extern_symbol_name
        .clone()
        .unwrap_or_else(|| function_name.to_string())
}

fn resolve_match_pattern<'a>(
    enum_def: &'a ir::EnumTypeDef,
    subject_ty: &str,
    pattern: &parser::MatchPattern,
) -> anyhow::Result<(&'a ir::EnumVariant, Option<String>)> {
    match pattern {
        parser::MatchPattern::Variant {
            type_name,
            variant_name,
            binder,
        } => {
            if type_name != subject_ty {
                bail!(
                    "match arm type {} does not match subject type {}",
                    type_name,
                    subject_ty
                );
            }
            let variant = enum_def
                .variants
                .iter()
                .find(|variant| variant.name == *variant_name)
                .with_context(|| {
                    format!(
                        "unknown variant {} for enum {} in LLVM lowering",
                        variant_name, enum_def.name
                    )
                })?;
            Ok((variant, binder.clone()))
        }
    }
}

fn llvm_byte_string_literal(bytes: &[u8]) -> String {
    let mut out = String::new();
    out.push_str("c\"");
    for byte in bytes {
        let value = *byte;
        if (0x20..=0x7e).contains(&value) && value != b'\\' && value != b'"' {
            out.push(char::from(value));
        } else {
            out.push_str(&format!("\\{:02X}", value));
        }
    }
    out.push('"');
    out
}

fn emit_extern_decl(name: &str, sig: &ExternSig) -> String {
    let mut args = sig
        .args
        .iter()
        .map(|arg| arg.as_ir().to_string())
        .collect::<Vec<_>>();
    if sig.variadic {
        args.push("...".to_string());
    }
    format!("declare {} @{}({})", sig.ret.as_ir(), name, args.join(", "))
}

fn type_ref_to_llvm(type_ref: &str, program: &ResolvedProgram) -> anyhow::Result<LlvmType> {
    let type_def = program
        .type_definitions
        .get(type_ref)
        .with_context(|| format!("unknown type {} for LLVM lowering", type_ref))?;

    match type_def {
        TypeDef::BuiltIn(BuiltInType::Bool)
        | TypeDef::BuiltIn(BuiltInType::U8)
        | TypeDef::BuiltIn(BuiltInType::I32) => Ok(LlvmType::I32),
        TypeDef::BuiltIn(BuiltInType::I64) => Ok(LlvmType::I64),
        TypeDef::BuiltIn(BuiltInType::FP32) => Ok(LlvmType::Float),
        TypeDef::BuiltIn(BuiltInType::FP64) => Ok(LlvmType::Double),
        TypeDef::BuiltIn(BuiltInType::Void) => Ok(LlvmType::Void),
        TypeDef::BuiltIn(BuiltInType::Semantic) => {
            bail!(
                "semantic builtin type {} cannot be lowered to LLVM",
                type_ref
            )
        }
        TypeDef::Struct(_) => Ok(LlvmType::I64),
        TypeDef::Enum(enum_def) => {
            if enum_def.is_tagged_union {
                Ok(LlvmType::I64)
            } else {
                Ok(LlvmType::I32)
            }
        }
    }
}

fn is_struct_type(program: &ResolvedProgram, type_ref: &str) -> bool {
    matches!(
        program.type_definitions.get(type_ref),
        Some(TypeDef::Struct(_))
    )
}

fn builtin_names() -> Vec<&'static str> {
    vec![
        "sum",
        "sub",
        "eq",
        "lt",
        "print",
        "i32_to_i64",
        "load_u8",
        "load_i32",
        "load_i64",
        "load_bool",
        "store_u8",
        "store_i32",
        "store_i64",
        "store_bool",
        "__string_payload",
        "__string_data_ptr",
        "__string_data_len",
        "char_at",
        "string_len",
        "slice",
        "print_str",
    ]
}

fn emit_builtin_functions(program: &ResolvedProgram) -> anyhow::Result<String> {
    let bytes_struct = runtime_layout::std_bytes_struct(program);
    let bytes_ptr_offset = runtime_layout::struct_field_offset(program, &bytes_struct, "ptr");
    let bytes_len_offset = runtime_layout::struct_field_offset(program, &bytes_struct, "len");
    let bytes_size = runtime_layout::struct_size_bytes(program, &bytes_struct);
    let string_enum = runtime_layout::std_string_enum(program);
    let string_heap_tag = runtime_layout::enum_variant_tag(&string_enum, "Heap");

    let mut out = String::new();
    out.push_str("define i32 @sum(i32 %a, i32 %b) {\n");
    out.push_str("entry:\n");
    out.push_str("  %c = add i32 %a, %b\n");
    out.push_str("  ret i32 %c\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @sub(i32 %a, i32 %b) {\n");
    out.push_str("entry:\n");
    out.push_str("  %c = sub i32 %a, %b\n");
    out.push_str("  ret i32 %c\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @eq(i32 %a, i32 %b) {\n");
    out.push_str("entry:\n");
    out.push_str("  %c = icmp eq i32 %a, %b\n");
    out.push_str("  %w = zext i1 %c to i32\n");
    out.push_str("  ret i32 %w\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @lt(i32 %a, i32 %b) {\n");
    out.push_str("entry:\n");
    out.push_str("  %c = icmp slt i32 %a, %b\n");
    out.push_str("  %w = zext i1 %c to i32\n");
    out.push_str("  ret i32 %w\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @print(i32 %a) {\n");
    out.push_str("entry:\n");
    out.push_str(&format!(
        "  %fmt = ptrtoint ptr @{} to i64\n",
        INTEGER_FMT_GLOBAL
    ));
    out.push_str("  %_ = call i32 (i64, ...) @printf(i64 %fmt, i32 %a)\n");
    out.push_str("  ret i32 0\n");
    out.push_str("}\n\n");

    out.push_str("define i64 @i32_to_i64(i32 %a) {\n");
    out.push_str("entry:\n");
    out.push_str("  %long = sext i32 %a to i64\n");
    out.push_str("  ret i64 %long\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @load_u8(i64 %addr) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  %b = load i8, ptr %p, align 1\n");
    out.push_str("  %w = zext i8 %b to i32\n");
    out.push_str("  ret i32 %w\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @load_i32(i64 %addr) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  %w = load i32, ptr %p, align 4\n");
    out.push_str("  ret i32 %w\n");
    out.push_str("}\n\n");

    out.push_str("define i64 @load_i64(i64 %addr) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  %l = load i64, ptr %p, align 8\n");
    out.push_str("  ret i64 %l\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @load_bool(i64 %addr) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  %raw = load i32, ptr %p, align 4\n");
    out.push_str("  %c = icmp ne i32 %raw, 0\n");
    out.push_str("  %w = zext i1 %c to i32\n");
    out.push_str("  ret i32 %w\n");
    out.push_str("}\n\n");

    out.push_str("define void @store_u8(i64 %addr, i32 %value) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  %v = trunc i32 %value to i8\n");
    out.push_str("  store i8 %v, ptr %p, align 1\n");
    out.push_str("  ret void\n");
    out.push_str("}\n\n");

    out.push_str("define void @store_i32(i64 %addr, i32 %value) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  store i32 %value, ptr %p, align 4\n");
    out.push_str("  ret void\n");
    out.push_str("}\n\n");

    out.push_str("define void @store_i64(i64 %addr, i64 %value) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  store i64 %value, ptr %p, align 8\n");
    out.push_str("  ret void\n");
    out.push_str("}\n\n");

    out.push_str("define void @store_bool(i64 %addr, i32 %value) {\n");
    out.push_str("entry:\n");
    out.push_str("  %p = inttoptr i64 %addr to ptr\n");
    out.push_str("  store i32 %value, ptr %p, align 4\n");
    out.push_str("  ret void\n");
    out.push_str("}\n\n");

    out.push_str("define internal i64 @__string_payload(i64 %s) {\n");
    out.push_str("entry:\n");
    out.push_str(&format!(
        "  %payload_addr = add i64 %s, {}\n",
        runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
    ));
    out.push_str("  %payload_ptr = inttoptr i64 %payload_addr to ptr\n");
    out.push_str("  %payload = load i64, ptr %payload_ptr, align 8\n");
    out.push_str("  ret i64 %payload\n");
    out.push_str("}\n\n");

    out.push_str("define internal i64 @__string_data_ptr(i64 %s) {\n");
    out.push_str("entry:\n");
    out.push_str("  %bytes = call i64 @__string_payload(i64 %s)\n");
    out.push_str(&format!("  %addr = add i64 %bytes, {}\n", bytes_ptr_offset));
    out.push_str("  %ptr = inttoptr i64 %addr to ptr\n");
    out.push_str("  %value = load i64, ptr %ptr, align 8\n");
    out.push_str("  ret i64 %value\n");
    out.push_str("}\n\n");

    out.push_str("define internal i32 @__string_data_len(i64 %s) {\n");
    out.push_str("entry:\n");
    out.push_str("  %bytes = call i64 @__string_payload(i64 %s)\n");
    out.push_str(&format!("  %addr = add i64 %bytes, {}\n", bytes_len_offset));
    out.push_str("  %ptr = inttoptr i64 %addr to ptr\n");
    out.push_str("  %value = load i32, ptr %ptr, align 4\n");
    out.push_str("  ret i32 %value\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @char_at(i64 %s, i32 %index) {\n");
    out.push_str("entry:\n");
    out.push_str("  %base = call i64 @__string_data_ptr(i64 %s)\n");
    out.push_str("  %idx = call i64 @i32_to_i64(i32 %index)\n");
    out.push_str("  %addr = add i64 %base, %idx\n");
    out.push_str("  %ptr = inttoptr i64 %addr to ptr\n");
    out.push_str("  %ch = load i8, ptr %ptr, align 1\n");
    out.push_str("  %wch = zext i8 %ch to i32\n");
    out.push_str("  ret i32 %wch\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @string_len(i64 %s) {\n");
    out.push_str("entry:\n");
    out.push_str("  %len = call i32 @__string_data_len(i64 %s)\n");
    out.push_str("  ret i32 %len\n");
    out.push_str("}\n\n");

    out.push_str("define i64 @slice(i64 %s, i32 %start, i32 %len) {\n");
    out.push_str("entry:\n");
    out.push_str("  %src_base = call i64 @__string_data_ptr(i64 %s)\n");
    out.push_str("  %len_plus_one = add i32 %len, 1\n");
    out.push_str("  %alloc_size = call i64 @i32_to_i64(i32 %len_plus_one)\n");
    out.push_str("  %dst = call i64 @malloc(i64 %alloc_size)\n");
    out.push_str("  %start_i64 = call i64 @i32_to_i64(i32 %start)\n");
    out.push_str("  %src = add i64 %src_base, %start_i64\n");
    out.push_str("  %copy_n = call i64 @i32_to_i64(i32 %len)\n");
    out.push_str("  %_cp = call i64 @memcpy(i64 %dst, i64 %src, i64 %copy_n)\n");
    out.push_str("  %nul_addr = add i64 %dst, %copy_n\n");
    out.push_str("  %nul_ptr = inttoptr i64 %nul_addr to ptr\n");
    out.push_str("  store i8 0, ptr %nul_ptr, align 1\n");

    out.push_str(&format!(
        "  %bytes_ptr = call i64 @malloc(i64 {})\n",
        bytes_size
    ));
    out.push_str(&format!(
        "  %bytes_ptr_addr = add i64 %bytes_ptr, {}\n",
        bytes_ptr_offset
    ));
    out.push_str("  %bytes_ptr_ptr = inttoptr i64 %bytes_ptr_addr to ptr\n");
    out.push_str("  store i64 %dst, ptr %bytes_ptr_ptr, align 8\n");
    out.push_str(&format!(
        "  %bytes_len_addr = add i64 %bytes_ptr, {}\n",
        bytes_len_offset
    ));
    out.push_str("  %bytes_len_ptr = inttoptr i64 %bytes_len_addr to ptr\n");
    out.push_str("  store i32 %len, ptr %bytes_len_ptr, align 4\n");

    out.push_str(&format!(
        "  %string_ptr = call i64 @malloc(i64 {})\n",
        runtime_layout::TAGGED_UNION_SIZE_BYTES
    ));
    out.push_str("  %string_tag_ptr = inttoptr i64 %string_ptr to ptr\n");
    out.push_str(&format!(
        "  store i32 {}, ptr %string_tag_ptr, align 4\n",
        string_heap_tag
    ));
    out.push_str(&format!(
        "  %payload_addr = add i64 %string_ptr, {}\n",
        runtime_layout::TAGGED_UNION_PAYLOAD_OFFSET_BYTES
    ));
    out.push_str("  %payload_ptr = inttoptr i64 %payload_addr to ptr\n");
    out.push_str("  store i64 %bytes_ptr, ptr %payload_ptr, align 8\n");
    out.push_str("  ret i64 %string_ptr\n");
    out.push_str("}\n\n");

    out.push_str("define i32 @print_str(i64 %s) {\n");
    out.push_str("entry:\n");
    out.push_str("  %ptr = call i64 @__string_data_ptr(i64 %s)\n");
    out.push_str("  %len = call i32 @__string_data_len(i64 %s)\n");
    out.push_str("  %len_i64 = call i64 @i32_to_i64(i32 %len)\n");
    out.push_str("  %_w = call i64 @write(i32 1, i64 %ptr, i64 %len_i64)\n");
    out.push_str(&format!(
        "  %nl = ptrtoint ptr @{} to i64\n",
        PRINT_STR_NEWLINE_GLOBAL
    ));
    out.push_str("  %_wn = call i64 @write(i32 1, i64 %nl, i64 1)\n");
    out.push_str("  ret i32 0\n");
    out.push_str("}\n");

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::compile;
    use crate::{ir, parser, tokenizer};

    fn compile_source_to_llvm(source: &str) -> String {
        let tokens = tokenizer::tokenize(source.to_string()).expect("tokenize source");
        let ast = parser::parse(tokens).expect("parse source");
        let resolved = ir::resolve(ast).expect("resolve source");
        compile(&resolved).expect("compile to llvm")
    }

    #[test]
    fn llvm_direct_compile_smoke() {
        let llvm = compile_source_to_llvm(
            r#"
fun main() -> I32 {
  print(1)
  return 0
}
"#,
        );
        assert!(llvm.contains("define i32 @main()"));
    }

    #[test]
    fn llvm_struct_assignment_call_return_use_copy_barriers() {
        let llvm = compile_source_to_llvm(
            r#"
struct Pair {
  a: I32,
  b: I32,
}

fun id(v: Pair) -> Pair {
  return v
}

fun main() -> I32 {
  p = Pair struct { a: 1, b: 2, }
  q = id(p)
  r = q
  print(r.a)
  return 0
}
"#,
        );
        assert!(llvm.contains("@calloc"));
        assert!(llvm.contains("@memcpy"));
    }

    #[test]
    fn llvm_struct_equality_uses_memcmp() {
        let llvm = compile_source_to_llvm(
            r#"
struct S {
  x: I32,
}

fun main() -> I32 {
  a = S struct { x: 1, }
  b = S struct { x: 1, }
  if a == b {
    print(1)
  }
  return 0
}
"#,
        );
        assert!(llvm.contains("@memcmp"));
    }

    #[test]
    fn llvm_assert_emits_exit_242() {
        let llvm = compile_source_to_llvm(
            r#"
fun main() -> I32 {
  assert(1 == 1)
  return 0
}
"#,
        );
        assert!(llvm.contains("call void @exit(i32 242)"));
    }

    #[test]
    fn llvm_prove_is_runtime_noop() {
        let llvm = compile_source_to_llvm(
            r#"
fun main() -> I32 {
  prove(1 == 1)
  return 0
}
"#,
        );
        assert!(!llvm.contains("@exit(i32 242)"));
    }

    #[test]
    fn llvm_extern_symbol_mapping_uses_extern_symbol_name() {
        let llvm = compile_source_to_llvm(
            r#"
namespace Clib {
  extern fun puts(v: PtrInt) -> I32
}

fun main() -> I32 {
  Clib.puts(i32_to_i64(0))
  return 0
}
"#,
        );
        assert!(llvm.contains("call i32 @puts("));
        assert!(llvm.contains("declare i32 @puts(i64)"));
    }

    #[test]
    fn llvm_namespace_calls_use_mangled_internal_symbol() {
        let llvm = compile_source_to_llvm(
            r#"
namespace Math {
  fun inc(v: I32) -> I32 {
    return v + 1
  }
}

fun main() -> I32 {
  return Math.inc(41)
}
"#,
        );
        assert!(llvm.contains("define i32 @Math__inc(i32 %arg0)"));
        assert!(llvm.contains("call i32 @Math__inc(i32 41)"));
    }
}
