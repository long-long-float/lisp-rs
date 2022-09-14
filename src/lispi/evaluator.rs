use anyhow::{anyhow, Result};
use rustc_hash::FxHashMap;
use std::{collections::HashMap, collections::LinkedList};

use super::{console::*, error::*, parser::*, SymbolValue, TokenLocation};

macro_rules! bug {
    () => {
        bug!("".to_string())
    };
    ( $msg:expr ) => {
        Error::Bug {
            message: $msg,
            file: file!(),
            line: line!(),
        }
        .with_null_location()
        .into()
    };
}

macro_rules! match_call_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        if let Some(ValueWithType { value: $p, type_: _ }) = $args.get($index) {
            $b
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),*, $b:block, $index:expr ) => {
        if let Some(ValueWithType { value: $p, type_: _ }) = $args.get($index) {
            match_call_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            Err(bug!(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))))
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        match_call_args!($args, $( $ps ),+, $b, 0)
    };
}

fn get_location(ast: Option<&AstWithLocation>) -> TokenLocation {
    ast.and_then(|arg| Some(arg.location))
        .unwrap_or(TokenLocation::Null)
}

macro_rules! match_special_args {
    ( $args:expr, $p:pat, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            if $index != $args.len() - 1 {
                let loc = get_location($args.get($index));
                Err(anyhow!(Error::Eval(format!("The length of argument is invalid")).with_location(loc)))
            }
            else {
                $b
            }
        }
        else {
            let loc = get_location($args.last());
            Err(Error::Eval(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $p:pat, $( $ps:pat ),+, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_special_args!($args, $( $ps ),*, $b, ($index + 1))
        }
        else {
            let loc = get_location($args.last());
            Err(Error::Eval(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $( $ps:pat ),+, $b:block ) => {
        match_special_args!($args, $( $ps ),+, $b, 0)
    };
}

macro_rules! match_special_args_with_rest {
    ( $args:expr, $rest:ident, $p:pat, $b:block, $index:expr ) => {
        if let (Some($p), (_, $rest)) = ($args.get($index), $args.split_at($index + 1)) {
            $b
        }
        else {
            let loc = get_location($args.last());
            Err(Error::Eval(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $rest:ident, $p:pat, $( $ps:pat ),+, $b:block, $index:expr ) => {
        if let Some($p) = $args.get($index) {
            match_special_args_with_rest!($args, $rest, $( $ps ),*, $b, ($index + 1))
        }
        else {
            let loc = get_location($args.last());
            Err(Error::Eval(format!("Cannot match {} with {:?}", stringify!($p), $args.get($index))).with_location(loc).into())
        }
    };

    ( $args:expr, $rest:ident, $( $ps:pat ),+, $b:block ) => {
        match_special_args_with_rest!($args, $rest, $( $ps ),+, $b, 0)
    };
}

macro_rules! ast_pat {
    ( $p:pat ) => {
        AstWithLocation {
            ast: $p,
            location: _,
        }
    };

    ( $p:pat, $loc:pat ) => {
        AstWithLocation {
            ast: $p,
            location: $loc,
        }
    };
}

// type EvalResult = Result<ValueWithType, Error>;
type EvalResult = Result<ValueWithType>;

#[derive(Clone, PartialEq, Debug)]
pub enum Value {
    Integer(i32),
    Float(f32),
    Boolean(bool),
    Char(char),
    String(String),
    Symbol(SymbolValue),
    List(Vec<ValueWithType>),
    Function {
        name: SymbolValue,
        args: Vec<SymbolValue>,
        body: Vec<AstWithLocation>,
        is_macro: bool,
    },
    NativeFunction {
        name: SymbolValue,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    },

    // For macro expansion
    RawAst(AstWithLocation),

    // For optimizing tail recursion
    Continue(String),
}

impl Value {
    pub fn nil() -> Value {
        Value::List(Vec::new())
    }

    fn is_true(&self) -> bool {
        match self {
            Value::Boolean(false) => false,
            _ => true,
        }
    }

    fn get_type(&self) -> Type {
        match self {
            Value::Integer(_) => Type::Int,
            Value::Float(_) => Type::Float,
            Value::Symbol(_) => Type::symbol(),
            Value::Boolean(_) => Type::Boolean,
            Value::Char(_) => Type::Char,
            Value::String(_) => Type::String,
            Value::List(_) => Type::list(),
            Value::Function {
                name: _,
                args: _,
                body: _,
                is_macro: _,
            } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::NativeFunction { name: _, func: _ } => {
                // TODO: Return concrete type
                Type::Any
            }
            Value::RawAst(_) => Type::Any,
            Value::Continue(_) => Type::Any,
        }
    }

    pub fn with_type(self) -> ValueWithType {
        let type_ = self.get_type();
        ValueWithType { value: self, type_ }
    }
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Integer(v) => write!(f, "{}", v),
            Value::Float(v) => write!(f, "{}", v),
            Value::Symbol(v) => write!(f, "{}", v.value),
            Value::Boolean(v) => write!(f, "{}", v),
            Value::Char(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
            Value::List(vs) => {
                if vs.len() == 0 {
                    write!(f, "Nil")
                } else {
                    write!(f, "(")?;
                    for (i, v) in vs.iter().enumerate() {
                        write!(f, "{}", v.value)?;
                        if i < vs.len() - 1 {
                            write!(f, " ")?;
                        }
                    }
                    write!(f, ")")?;
                    Ok(())
                }
            }
            Value::Function {
                name,
                args: _,
                body: _,
                is_macro,
            } => {
                if *is_macro {
                    write!(f, "MACRO {}", name.value)
                } else {
                    write!(f, "FUNCTION {}", name.value)
                }
            }
            Value::NativeFunction { name, func: _ } => {
                write!(f, "FUNCTION {}", name.value)
            }
            Value::RawAst(ast) => write!(f, "AST {:?}", ast),
            Value::Continue(name) => write!(f, "CONINUE {:?}", name),
        }
    }
}

impl From<&Ast> for Value {
    fn from(ast: &Ast) -> Self {
        match ast {
            Ast::Integer(v) => Value::Integer(*v),
            Ast::Float(v) => Value::Float(*v),
            Ast::Boolean(v) => Value::Boolean(*v),
            Ast::Char(v) => Value::Char(*v),
            Ast::String(v) => Value::String(v.clone()),
            Ast::Symbol(v) => Value::Symbol(v.clone()),
            Ast::Quoted(v) => Value::from(&(*v).ast),
            Ast::List(vs) => {
                let vs = vs.iter().map(|v| Value::from(&v.ast).with_type()).collect();
                Value::List(vs)
            }
            Ast::Nil => Value::nil(),
            Ast::Continue(v) => Value::Continue(v.clone()),
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Boolean(value)
    }
}

pub struct Environment {
    local_stack: LinkedList<Local>,
    pub sym_table: SymbolTable,
}

impl Environment {
    pub fn new() -> Environment {
        let mut env = Environment {
            local_stack: LinkedList::new(),
            sym_table: SymbolTable::new(),
        };
        env.push_local();
        env
    }

    fn update_var(&mut self, name: SymbolValue, value: ValueWithType) -> Result<(), Error> {
        if let Some(found) = self.find_var_mut(&name) {
            // TODO: Check type
            found.value = value.value;
            Ok(())
        } else {
            Err(Error::Eval(format!(
                "A variable `{}` is not defined.",
                name.value
            )))
        }
    }

    fn resolve_sym_id(&mut self, name: &SymbolValue) -> u32 {
        if name.id != 0 {
            name.id
        } else {
            self.sym_table.find_id_or_insert(&name.value)
        }
    }

    fn insert_var(&mut self, name: SymbolValue, value: ValueWithType) {
        let id = self.resolve_sym_id(&name);
        // local_stack must have least one local
        let local = self.local_stack.front_mut().unwrap();
        local.variables.insert(id, value);
    }

    fn find_var(&mut self, name: &SymbolValue) -> Option<&ValueWithType> {
        let id = self.resolve_sym_id(&name);
        for local in &self.local_stack {
            if let Some(value) = local.variables.get(&id) {
                return Some(value);
            }
        }
        None
    }

    fn find_var_mut(&mut self, name: &SymbolValue) -> Option<&mut ValueWithType> {
        let id = self.resolve_sym_id(&name);
        for local in self.local_stack.iter_mut() {
            if let Some(value) = local.variables.get_mut(&id) {
                return Some(value);
            }
        }
        None
    }

    fn insert_function(
        &mut self,
        name: &str,
        type_: Type,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    ) {
        let name = name.to_string();
        let id = self.sym_table.find_id_or_insert(&name);
        let sym = SymbolValue { value: name, id };
        self.insert_var(
            sym.clone(),
            ValueWithType {
                value: Value::NativeFunction { name: sym, func },
                type_,
            },
        );
    }

    fn insert_variable_as_symbol(&mut self, name: &str) {
        let name = name.to_string();
        let id = self.sym_table.find_id_or_insert(&name);
        let sym = SymbolValue { value: name, id };
        self.insert_var(sym.clone(), Value::Symbol(sym).with_type());
    }

    fn push_local(&mut self) {
        self.local_stack.push_front(Local::new());
    }

    fn pop_local(&mut self) {
        self.local_stack.pop_front();
    }
}

struct Local {
    variables: FxHashMap<u32, ValueWithType>,
    // For ID=0 symbols
    // variables_string: HashMap<String, ValueWithType>,
}

impl Local {
    fn new() -> Local {
        Local {
            variables: HashMap::default(),
        }
    }
}

#[derive(Clone, PartialEq, Debug)]
pub struct ValueWithType {
    pub value: Value,
    pub type_: Type,
}

#[derive(Clone, PartialEq, Debug)]
pub enum Type {
    Numeric,
    Int,
    Float,
    Boolean,
    Char,
    String,

    Scala(String),
    Composite {
        name: String,
        inner: Vec<Box<Type>>,
    },
    Function {
        args: Vec<Box<Type>>,
        result: Box<Type>,
    },
    Any,
}

impl Type {
    fn scala(name: &str) -> Type {
        Type::Scala(name.to_string())
    }

    fn int() -> Type {
        Type::Int
    }

    fn symbol() -> Type {
        Type::scala("symbol")
    }

    fn list() -> Type {
        Type::Composite {
            name: "list".to_string(),
            inner: Vec::new(),
        }
    }

    fn function(args: Vec<Type>, result: Type) -> Type {
        Type::Function {
            args: args.iter().map(|a| Box::new(a.clone())).collect(),
            result: Box::new(result),
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Type::Numeric => write!(f, "numeric"),
            Type::Int => write!(f, "int"),
            Type::Float => write!(f, "float"),
            Type::Boolean => write!(f, "boolean"),
            Type::Char => write!(f, "char"),
            Type::String => write!(f, "string"),
            Type::Scala(name) => write!(f, "{}", name),
            Type::Composite { name, inner } => {
                let inner = inner
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "{}({})", name, inner)
            }
            Type::Function { args, result } => {
                let args = args
                    .iter()
                    .map(|t| format!("{}", *t))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, "({}) -> {}", args, *result)
            }
            Type::Any => write!(f, "any"),
        }
    }
}

fn check_arg_types(
    func_loc: TokenLocation,
    args: &[ValueWithType],
    arg_locs: &[TokenLocation],
    expected_types: &[Type],
) -> Result<()> {
    if args.len() != expected_types.len() {
        return Err(Error::Type(format!(
            "{} arguments are expected, but {} arguments are specified.",
            expected_types.len(),
            args.len()
        ))
        .with_location(func_loc)
        .into());
    }

    for (i, (a, expected)) in args.iter().zip(expected_types).enumerate() {
        match (&a.type_, expected) {
            (Type::Any, _) | (_, Type::Any) => (), // Pass-through
            (Type::Int, Type::Numeric) | (Type::Float, Type::Numeric) => (), // numeric includes int and float
            (actual, expected) => {
                if actual != expected {
                    let loc = arg_locs.get(i).unwrap_or(&TokenLocation::Null);
                    return Err(Error::Type(format!(
                        "Expected the type {} , but the actual type is {}",
                        expected, actual
                    ))
                    .with_location(*loc)
                    .into());
                }
            }
        }
    }

    Ok(())
}

pub fn eval_asts(asts: &[AstWithLocation], env: &mut Environment) -> Result<Vec<ValueWithType>> {
    asts.iter()
        .map(|arg| eval_ast(arg, env))
        .collect::<Result<Vec<ValueWithType>>>()
}

fn get_last_result(results: Vec<ValueWithType>) -> ValueWithType {
    results
        .into_iter()
        .last()
        .unwrap_or(Value::nil().with_type())
}

fn get_symbol_values(symbols: &Vec<AstWithLocation>) -> Result<Vec<SymbolValue>> {
    symbols
        .iter()
        .map(|symbol| {
            if let Ast::Symbol(v) = &symbol.ast {
                Ok(v.clone())
            } else {
                Err(Error::Eval(format!("{:?} is not an symbol", symbol.ast))
                    .with_location(symbol.location)
                    .into())
            }
        })
        .collect()
}

/// Try to optimize tail recursion for body
// TOOD: Support body what the function is assigned other variable
fn optimize_tail_recursion(
    func_name: &String,
    locals: &[SymbolValue],
    body: &[AstWithLocation],
) -> Option<Vec<AstWithLocation>> {
    /// Optimize tail recursion for the last ast
    /// ref https://people.csail.mit.edu/jaffer/r5rs/Proper-tail-recursion.html
    fn _optimize_tail_recursion(
        func_name: &String,
        locals: &[SymbolValue],
        ast: &AstWithLocation,
    ) -> Option<AstWithLocation> {
        match &ast.ast {
            Ast::List(vs) => {
                if let Some((name_ast, args)) = vs.split_first() {
                    if let Ast::Symbol(name) = &name_ast.ast {
                        let name = name.value.as_str();
                        let mut args = match name {
                            "begin" => optimize_tail_recursion(func_name, locals, args),
                            "if" => {
                                let cond = args.get(0)?;
                                if let (Some(then), Some(els)) = (args.get(1), args.get(2)) {
                                    let then = _optimize_tail_recursion(func_name, locals, then)?;
                                    let els = _optimize_tail_recursion(func_name, locals, els)?;
                                    Some(vec![cond.clone(), then, els])
                                } else if let Some(then) = args.get(1) {
                                    let then = _optimize_tail_recursion(func_name, locals, then)?;
                                    Some(vec![cond.clone(), then])
                                } else {
                                    None
                                }
                            }
                            "let" | "let*" => {
                                let (proc_id, rest) = match args.split_first() {
                                    Some((ast_pat!(Ast::Symbol(proc_id)), rest)) => {
                                        (Some(proc_id), rest)
                                    }
                                    _ => (None, args),
                                };
                                if let Some((ast_pat!(Ast::List(vars)), body)) = rest.split_first()
                                {
                                    let includes_sym_in_vars = vars.iter().any(|var| {
                                        if let ast_pat!(Ast::List(var)) = var {
                                            if let Some(expr) = var.get(1) {
                                                includes_symbol(func_name, &expr.ast)
                                            } else {
                                                false
                                            }
                                        } else {
                                            false
                                        }
                                    });

                                    if includes_sym_in_vars {
                                        return None;
                                    }

                                    let mut body =
                                        optimize_tail_recursion(func_name, locals, body)?;

                                    let mut form = Vec::new();
                                    if let Some(proc_id) = proc_id {
                                        form.push(
                                            Ast::Symbol(proc_id.clone()).with_null_location(),
                                        );
                                    }
                                    form.push(Ast::List(vars.clone()).with_null_location());
                                    form.append(&mut body);
                                    Some(form)
                                } else {
                                    None
                                }
                            }
                            _ => {
                                let not_in_args =
                                    args.iter().all(|arg| !includes_symbol(func_name, &arg.ast));
                                if name == func_name && not_in_args {
                                    let mut form = vec![Ast::Symbol(SymbolValue::without_id(
                                        "begin".to_string(),
                                    ))
                                    .with_null_location()];

                                    let mut args = args
                                        .iter()
                                        .zip(locals)
                                        .map(|(arg, sym)| {
                                            Ast::List(vec![
                                                Ast::Symbol(SymbolValue::without_id(
                                                    "set!".to_string(),
                                                ))
                                                .with_null_location(),
                                                Ast::Symbol(sym.clone()).with_null_location(),
                                                arg.clone(),
                                            ])
                                            .with_null_location()
                                        })
                                        .collect::<Vec<_>>();

                                    form.append(&mut args);
                                    form.push(Ast::Continue(name.to_string()).with_null_location());

                                    return Some(Ast::List(form).with_null_location());
                                } else {
                                    // println!("[Warn] '{}' is treated as an ordinay function in optimizing tail recursion", name);

                                    let args = args
                                        .iter()
                                        .map(|arg| _optimize_tail_recursion(func_name, locals, arg))
                                        .collect::<Option<Vec<_>>>()?;

                                    Some(args)
                                }
                            }
                        };
                        args.as_mut().map(|args| {
                            let mut whole = vec![name_ast.clone()];
                            whole.append(args);
                            Ast::List(whole).with_null_location()
                        })
                    } else {
                        // This is not valid ast
                        None
                    }
                } else {
                    Some(ast.clone())
                }
            }
            Ast::Quoted(v) => _optimize_tail_recursion(func_name, locals, &v),
            Ast::Symbol(_)
            | Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil => Some(ast.clone()),
            Ast::Continue(_) => Some(ast.clone()),
        }
    }

    fn includes_symbol(sym: &String, ast: &Ast) -> bool {
        match ast {
            Ast::List(vs) => vs.iter().any(|v| includes_symbol(sym, &v.ast)),
            Ast::Quoted(v) => includes_symbol(sym, &v.ast),
            Ast::Symbol(v) => &v.value == sym,
            Ast::Integer(_)
            | Ast::Float(_)
            | Ast::Boolean(_)
            | Ast::Char(_)
            | Ast::String(_)
            | Ast::Nil => false,
            Ast::Continue(_) => false,
        }
    }

    let len = body.len();
    match len {
        0 => None,
        _ => {
            let (last, body) = body.split_last().unwrap();
            for ast in body {
                if includes_symbol(func_name, &ast.ast) {
                    return None;
                }
            }
            _optimize_tail_recursion(func_name, locals, last).map(|last| {
                let mut body = body.to_vec();
                body.push(last);
                body
            })
        }
    }
}

fn eval_special_form(
    name_ast: &AstWithLocation,
    raw_args: &[AstWithLocation],
    env: &mut Environment,
) -> EvalResult {
    if let Ast::Symbol(name) = &name_ast.ast {
        let name = name.value.as_str();
        match name {
            "set!" => {
                match_special_args!(raw_args, ast_pat!(Ast::Symbol(name), _loc), value, {
                    let value = eval_ast(value, env)?;
                    env.update_var(name.clone(), value)
                        .or_else(|err| Err(anyhow!(err.with_location(name_ast.location))))?;
                    Ok(Value::nil().with_type())
                })
            }
            "define" => {
                match_special_args!(raw_args, ast_pat!(Ast::Symbol(name), _loc), value, {
                    let value = eval_ast(value, env)?;

                    env.insert_var(name.clone(), value);

                    Ok(Value::nil().with_type())
                })
            }
            "define-macro" => {
                match_special_args_with_rest!(
                    raw_args,
                    body,
                    ast_pat!(Ast::Symbol(fun_name), _loc1),
                    ast_pat!(Ast::List(args)),
                    {
                        let is_macro = name == "define-macro";

                        let args = get_symbol_values(args)?;

                        let arg_types = args.iter().map(|_| Type::Any).collect();
                        let func = Value::Function {
                            name: fun_name.clone(),
                            args: args,
                            body: body.to_vec(),
                            is_macro,
                        };
                        env.insert_var(
                            fun_name.clone(),
                            ValueWithType {
                                value: func,
                                type_: Type::function(arg_types, Type::Any),
                            },
                        );

                        Ok(Value::nil().with_type())
                    }
                )
            }
            "lambda" => {
                match_special_args_with_rest!(raw_args, body, ast_pat!(Ast::List(args), _loc), {
                    let args = get_symbol_values(args)?;

                    let arg_types = args.iter().map(|_| Type::Any).collect();
                    let func = Value::Function {
                        name: SymbolValue::empty(),
                        args: args,
                        body: body.to_vec(),
                        is_macro: false,
                    };

                    Ok(ValueWithType {
                        value: func,
                        type_: Type::function(arg_types, Type::Any),
                    })
                })
            }
            "let" | "let*" => {
                let err = Err(Error::Eval(
                    "'let' is formed as (let ([id expr] ...) body ...) or named let (let proc-id ([id expr] ...) body ...)".to_string(),
                ).with_location(name_ast.location).into());

                let sequence = name == "let*";

                if let Some((ast_pat!(Ast::List(vars), _loc), body)) = raw_args.split_first() {
                    env.push_local();

                    let mut exprs = Vec::new();

                    for var in vars {
                        if let ast_pat!(Ast::List(var)) = var {
                            match_special_args!(var, ast_pat!(Ast::Symbol(id)), expr, {
                                let expr = eval_ast(expr, env)?;
                                if sequence {
                                    env.insert_var(id.clone(), expr);
                                } else {
                                    exprs.push((id, expr));
                                }
                                Ok(())
                            })?
                        } else {
                            return err;
                        }
                    }

                    if !sequence {
                        for (id, expr) in exprs {
                            env.insert_var(id.clone(), expr);
                        }
                    }

                    let result = eval_asts(body, env);

                    env.pop_local();

                    Ok(get_last_result(result?))
                } else if let (
                    Some(ast_pat!(Ast::Symbol(proc_id))),
                    Some(ast_pat!(Ast::List(args))),
                    (_, body),
                ) = (raw_args.get(0), raw_args.get(1), raw_args.split_at(2))
                {
                    // named let

                    let mut arg_exprs = Vec::new();
                    for arg in args {
                        if let ast_pat!(Ast::List(var)) = arg {
                            match_special_args!(var, ast_pat!(Ast::Symbol(id)), expr, {
                                arg_exprs.push((id.clone(), expr.clone()));
                                Ok(())
                            })?
                        } else {
                            return err;
                        }
                    }
                    let (args, exprs): (Vec<SymbolValue>, Vec<_>) = arg_exprs.into_iter().unzip();

                    if let Some(optimized) = optimize_tail_recursion(&proc_id.value, &args, body) {
                        // println!("Tail recursion!");
                        // println!("{:#?}", optimized);

                        env.push_local();

                        // Sequencial initialization
                        for (id, expr) in args.iter().zip(exprs) {
                            let expr = eval_ast(&expr, env)?;
                            env.insert_var(id.clone(), expr);
                        }

                        // let mut result: ValueWithType;
                        let result = loop {
                            let results = eval_asts(&optimized, env);
                            let result = get_last_result(results?);
                            if let Value::Continue(id) = &result.value {
                                if id == &proc_id.value {
                                    // continue
                                } else {
                                    break result;
                                }
                            } else {
                                break result;
                            }
                        };

                        env.pop_local();

                        Ok(result)
                    } else {
                        let func = Value::Function {
                            name: proc_id.clone(),
                            args,
                            body: body.to_vec(),
                            is_macro: false,
                        };

                        env.push_local();
                        env.insert_var(proc_id.clone(), func.with_type());

                        let mut call_args = vec![Ast::Symbol(proc_id.clone()).with_null_location()];
                        let mut exprs = exprs;
                        call_args.append(&mut exprs);

                        let result =
                            eval_asts(&vec![Ast::List(call_args).with_null_location()], env);

                        env.pop_local();

                        Ok(get_last_result(result?))
                    }
                } else {
                    err
                }
            }

            "begin" => Ok(get_last_result(eval_asts(raw_args, env)?)),
            "if" => {
                if let (Some(cond), Some(then_ast)) = (raw_args.get(0), raw_args.get(1)) {
                    let cond = eval_ast(cond, env)?.value.is_true();
                    if cond {
                        eval_ast(then_ast, env)
                    } else {
                        if let Some(else_ast) = raw_args.get(2) {
                            eval_ast(else_ast, env)
                        } else {
                            Ok(Value::nil().with_type())
                        }
                    }
                } else {
                    Err(
                        Error::Eval("'if' is formed as (if cond then else)".to_string())
                            .with_location(name_ast.location)
                            .into(),
                    )
                }
            }
            "when" | "unless" => {
                let invert = name == "unless";
                if let Some((cond, forms)) = raw_args.split_first() {
                    let cond = eval_ast(cond, env)?.value.is_true();
                    let cond = if invert { !cond } else { cond };
                    if cond {
                        Ok(get_last_result(eval_asts(forms, env)?))
                    } else {
                        Ok(Value::nil().with_type())
                    }
                } else {
                    Err(
                        Error::Eval(format!("'{}' is formed as (if cond then else)", name))
                            .with_location(name_ast.location)
                            .into(),
                    )
                }
            }
            "cond" => {
                let err = Err(Error::Eval(
                    "'cond' is formed as (cond (cond body ...) ...)".to_string(),
                )
                .with_location(name_ast.location)
                .into());

                for arg in raw_args {
                    if let ast_pat!(Ast::List(arm)) = arg {
                        if let Some((cond, body)) = arm.split_first() {
                            let cond = eval_ast(cond, env)?;
                            if cond.value.is_true() {
                                return Ok(get_last_result(eval_asts(body, env)?));
                            }
                        } else {
                            return err;
                        }
                    } else {
                        return err;
                    }
                }

                Ok(Value::nil().with_type())
            }
            "function" => {
                if let Some(func) = raw_args.first() {
                    let result = eval_ast(func, env)?;
                    if let Value::Symbol(name) = result.value {
                        Ok(eval_ast(&Ast::Symbol(name).with_null_location(), env)?)
                    } else {
                        Ok(result)
                    }
                } else {
                    Err(
                        Error::Eval("'function' is formed as (function name)".to_string())
                            .with_location(name_ast.location)
                            .into(),
                    )
                }
            }
            _ => {
                let mac = eval_ast(name_ast, env)?;
                if let Value::Function {
                    name: _,
                    args,
                    body,
                    is_macro: true,
                } = mac.value
                {
                    env.push_local();

                    for (name, value) in args.iter().zip(raw_args) {
                        env.insert_var(name.clone(), Value::RawAst(value.clone()).with_type());
                    }

                    let result = eval_asts(&body, env);

                    env.pop_local();

                    let result = get_last_result(result?);
                    eval_ast(&Ast::from(result.value).with_null_location(), env)
                } else {
                    Err(Error::DoNothing.with_null_location().into())
                }
            }
        }
    } else {
        Err(Error::DoNothing.with_null_location().into())
    }
}

fn eval_function(
    name: &AstWithLocation,
    args: &[AstWithLocation],
    env: &mut Environment,
) -> EvalResult {
    let name_loc = &name.location;
    let name = eval_ast(name, env)?;
    let arg_locs = args.iter().map(|arg| arg.location).collect::<Vec<_>>();
    let args = eval_asts(args, env)?;

    apply_function(&name, *name_loc, &args, &arg_locs, env)
}

fn apply_function(
    func: &ValueWithType,
    func_loc: TokenLocation,
    args: &[ValueWithType],
    arg_locs: &[TokenLocation],
    env: &mut Environment,
) -> EvalResult {
    if let ValueWithType {
        value: _,
        type_: Type::Function {
            args: arg_types,
            result: _,
        },
    } = &func
    {
        let arg_types = arg_types.iter().map(|a| *a.clone()).collect::<Vec<Type>>();
        check_arg_types(func_loc, args, arg_locs, &arg_types)?;
    }

    match &func.value {
        Value::Symbol(func_name) => {
            let func_name = func_name.value.as_str();

            match func_name {
                // Functions
                "+" | "-" | "*" | "/" | ">" | ">=" | "<" | "<=" => {
                    enum Number {
                        Int(i32),
                        Float(f32),
                    }

                    let mut has_float_arg = false;
                    let args = args
                        .iter()
                        .zip(arg_locs)
                        .map(|(arg, loc)| match arg.value {
                            Value::Integer(v) => Ok(Number::Int(v)),
                            Value::Float(v) => {
                                has_float_arg = true;
                                Ok(Number::Float(v))
                            }
                            _ => Err(Error::Eval(format!("`{}` is not an integer.", arg.value))
                                .with_location(*loc)
                                .into()),
                        })
                        .collect::<Result<Vec<Number>>>()?;

                    macro_rules! calc {
                        ( $args:expr, $elem_type:ty ) => {
                            match func_name {
                                "+" => $args.fold(0.0 as $elem_type, |sum, v| sum + v),
                                "*" => $args.fold(1.0 as $elem_type, |acc, v| acc * v),
                                "-" | "/" => {
                                    let sub = func_name == "-";
                                    if args.len() >= 2 {
                                        $args
                                            .reduce(|acc, v| if sub { acc - v } else { acc / v })
                                            .unwrap()
                                    } else if args.len() == 1 {
                                        let value = $args.nth(0).unwrap();
                                        if sub {
                                            0.0 as $elem_type - value
                                        } else {
                                            1.0 as $elem_type / value
                                        }
                                    } else {
                                        return Err(Error::Eval(format!(
                                            "Function {} needs least one value",
                                            func_name
                                        ))
                                        .with_location(func_loc)
                                        .into());
                                    }
                                }
                                ">" | ">=" | "<" | "<=" => {
                                    let args = $args.collect::<Vec<_>>();
                                    let x = args.get(0);
                                    let y = args.get(1);
                                    let res = match func_name {
                                        ">" => x > y,
                                        ">=" => x >= y,
                                        "<" => x < y,
                                        "<=" => x <= y,
                                        _ => return Err(bug!()),
                                    };
                                    return Ok(Value::from(res).with_type());
                                }
                                _ => {
                                    return Err(Error::Eval(format!(
                                        "Unknown function: {}",
                                        func_name
                                    ))
                                    .with_location(func_loc)
                                    .into())
                                }
                            }
                        };
                    }

                    if has_float_arg {
                        let mut args = args.iter().map(|arg| match arg {
                            &Number::Int(v) => v as f32,
                            &Number::Float(v) => v,
                        });
                        Ok(Value::Float(calc!(args, f32)).with_type())
                    } else {
                        let mut args = args.iter().map(|arg| match arg {
                            &Number::Int(v) => v,
                            &Number::Float(v) => v as i32,
                        });
                        Ok(Value::Integer(calc!(args, i32)).with_type())
                    }
                }
                "or" => Ok(Value::Boolean(args.iter().any(|arg| arg.value.is_true())).with_type()),
                "print" => {
                    for arg in args {
                        printlnuw(&arg.value);
                    }
                    Ok(Value::nil().with_type())
                }
                "display" => {
                    for arg in args {
                        print!("{}", arg.value);
                    }
                    Ok(Value::nil().with_type())
                }
                "list" => Ok(Value::List(args.to_vec()).with_type()),
                "map" => {
                    let err =
                        Error::Eval("'map' is formed as (mapcar function list ...)".to_string())
                            .with_location(func_loc);

                    if let Some((func, lists)) = args.split_first() {
                        let lists = lists
                            .iter()
                            .map(|list| {
                                if let Value::List(elements) = &list.value {
                                    Ok(elements)
                                } else {
                                    Err(anyhow!(err.clone()))
                                }
                            })
                            .collect::<Result<Vec<_>>>()?;

                        if lists.len() == 0 {
                            return Err(anyhow!(err.clone()));
                        }

                        let mut result = Vec::new();
                        let list0_len = lists.get(0).unwrap().len();
                        for idx in 0..list0_len {
                            let mut args = Vec::new();
                            for list in &lists {
                                args.push(
                                    list.get(idx)
                                        .map(|v| v.clone())
                                        .unwrap_or(Value::nil().with_type()),
                                );
                            }
                            let arg_locs = [TokenLocation::Null].repeat(lists.len());

                            result.push(apply_function(
                                func,
                                TokenLocation::Null,
                                &args,
                                &arg_locs,
                                env,
                            )?);
                        }

                        Ok(Value::List(result).with_type())
                    } else {
                        Err(anyhow!(err))
                    }
                }
                _ => Err(Error::Eval(format!("Unknown function: {}", func_name))
                    .with_location(func_loc)
                    .into()),
            }
        }
        Value::Function {
            name: _,
            args: arg_names,
            body,
            is_macro: false,
        } => {
            env.push_local();

            for (name, value) in arg_names.iter().zip(args) {
                env.insert_var(name.clone(), value.clone());
            }

            let result = eval_asts(&body, env);

            env.pop_local();

            Ok(get_last_result(result?))
        }
        Value::NativeFunction { name: _, func } => func(args.to_vec()),
        _ => Err(Error::Eval(format!("{} is not a function", func.value))
            .with_location(func_loc)
            .into()),
    }
}

fn eval_ast(ast: &AstWithLocation, env: &mut Environment) -> EvalResult {
    match &ast.ast {
        Ast::List(elements) => {
            if let Some((first, rest)) = elements.split_first() {
                let result = eval_special_form(first, rest, env);
                if let Err(err) = result {
                    if let Some(ErrorWithLocation {
                        err: Error::DoNothing,
                        location: _,
                    }) = err.downcast_ref::<ErrorWithLocation>()
                    {
                        eval_function(first, rest, env)
                    } else {
                        Err(anyhow!(err))
                    }
                } else {
                    result
                }
            } else {
                Ok(Value::nil().with_type())
            }
        }
        Ast::Symbol(value) => {
            if let Some(var) = env.find_var(&value) {
                Ok(var.clone())
            } else {
                Err(
                    Error::Eval(format!("A variable `{}` is not defined", value.value))
                        .with_location(ast.location)
                        .into(),
                )
            }
        }
        _ => Ok(Value::from(&ast.ast).with_type()),
    }
}

pub fn init_env(env: &mut Environment) {
    // Pre-defined functions and special forms
    // TODO: Add function symbols with its definition
    env.insert_function(
        "even?",
        Type::function(vec![Type::int()], Type::Any),
        |args| {
            match_call_args!(args, Value::Integer(v), {
                Ok(Value::from(v % 2 == 0).with_type())
            })
        },
    );
    env.insert_function(
        "=",
        Type::function(vec![Type::Any, Type::Any], Type::Any),
        |args| match_call_args!(args, v1, v2, { Ok(Value::from(v1 == v2).with_type()) }),
    );
    env.insert_function(
        "car",
        Type::function(vec![Type::list()], Type::Any),
        |args| {
            match_call_args!(args, Value::List(vs), {
                let first = vs.first().map(|v| (*v).clone());
                Ok(first.unwrap_or(Value::nil().with_type()))
            })
        },
    );
    env.insert_function(
        "cdr",
        Type::function(vec![Type::list()], Type::Any),
        |args| {
            match_call_args!(args, Value::List(vs), {
                if let Some((_, rest)) = vs.split_first() {
                    if rest.is_empty() {
                        Ok(Value::nil().with_type())
                    } else {
                        Ok(Value::List(rest.to_vec()).with_type())
                    }
                } else {
                    Ok(Value::nil().with_type())
                }
            })
        },
    );
    // TODO: Make mod to accept number
    env.insert_function(
        "mod",
        Type::function(vec![Type::int(), Type::int()], Type::int()),
        |args| {
            match_call_args!(args, Value::Integer(num), Value::Integer(divisor), {
                Ok(Value::Integer(num % divisor).with_type())
            })
        },
    );
    env.insert_function(
        "cons",
        Type::function(vec![Type::Any, Type::list()], Type::list()),
        |args| {
            match_call_args!(args, v, Value::List(vs), {
                let mut vs = vs.clone();
                vs.insert(0, v.clone().with_type());
                Ok(Value::List(vs).with_type())
            })
        },
    );
    env.insert_function(
        "length",
        Type::function(vec![Type::list()], Type::Int),
        |args| {
            match_call_args!(args, Value::List(vs), {
                Ok(Value::Integer(vs.len() as i32).with_type())
            })
        },
    );
    env.insert_function(
        "list-ref",
        Type::function(vec![Type::list(), Type::Int], Type::Any),
        |args| {
            match_call_args!(args, Value::List(vs), Value::Integer(idx), {
                if let Some(v) = vs.get(*idx as usize) {
                    Ok(v.clone())
                } else {
                    // TODO: Annotate the location
                    Err(Error::Eval("out of range".to_string())
                        .with_null_location()
                        .into())
                }
            })
        },
    );
    env.insert_function(
        "string->list",
        Type::function(vec![Type::String], Type::list()),
        |args| {
            match_call_args!(args, Value::String(value), {
                let chars = value.chars().map(|c| Value::Char(c).with_type()).collect();
                Ok(Value::List(chars).with_type())
            })
        },
    );
    env.insert_function("newline", Type::function(vec![], Type::Any), |_| {
        newlineuw();
        Ok(Value::List(vec![]).with_type())
    });

    env.insert_variable_as_symbol("print");
    env.insert_variable_as_symbol("display");
    env.insert_variable_as_symbol("list");
    env.insert_variable_as_symbol("+");
    env.insert_variable_as_symbol("-");
    env.insert_variable_as_symbol("*");
    env.insert_variable_as_symbol("/");
    env.insert_variable_as_symbol(">");
    env.insert_variable_as_symbol(">=");
    env.insert_variable_as_symbol("<");
    env.insert_variable_as_symbol("<=");
    env.insert_variable_as_symbol("or");
    env.insert_variable_as_symbol("map");
}

pub fn eval_program(asts: &Program, mut env: Environment) -> Result<Vec<ValueWithType>> {
    init_env(&mut env);
    eval_asts(asts, &mut env)
}
