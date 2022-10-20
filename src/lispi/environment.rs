use rustc_hash::FxHashMap;
use std::{cell::RefCell, collections::HashMap, rc::Rc};

use super::{console::*, error::*, evaluator::*, typer::*, SymbolValue};

pub struct Environment<T> {
    pub head_local: LocalRef<T>,
    /// For referencing variables from closure.
    pub lambda_local: LocalRef<T>,
}

impl<T> Environment<T>
where
    T: Clone + std::fmt::Debug,
{
    pub fn new() -> Environment<T> {
        let mut env = Environment {
            head_local: None,
            lambda_local: None,
        };
        env.push_local();
        env
    }

    pub fn update_var(&mut self, name: SymbolValue, value: &T) -> Result<(), Error> {
        let mut local = self.head_local.as_mut().unwrap().borrow_mut();
        if local.update_var(name.id, value) {
            Ok(())
        } else {
            Err(Error::Eval(format!(
                "A variable `{}` is not defined.",
                name.value
            )))
        }
    }

    pub fn insert_var(&mut self, name: SymbolValue, value: T) {
        // local_stack must have least one local
        let mut local = self.head_local.as_ref().unwrap().borrow_mut();
        local.variables.insert(name.id, value);
    }

    pub fn find_var(&mut self, name: &SymbolValue) -> Option<T> {
        self.head_local
            .as_mut()
            .unwrap()
            .borrow_mut()
            .find_var(name.id)
    }

    #[allow(dead_code)]
    fn dump_local(&self) {
        let local = self.head_local.as_ref().unwrap().borrow();
        printlnuw("--- Locals ---");
        local.dump();
    }

    pub fn push_local(&mut self) {
        let local = self.head_local.clone();
        let local = Some(Rc::new(RefCell::new(Local::new(local))));
        self.head_local = local;
    }

    pub fn pop_local(&mut self) {
        if let Some(local) = &self.head_local {
            let parent = local.borrow().parent.clone();
            self.head_local = parent;
        }
    }
}

impl Environment<ValueWithType> {
    pub fn insert_function(
        &mut self,
        name: SymbolValue,
        type_: Type,
        func: fn(Vec<ValueWithType>) -> EvalResult,
    ) {
        self.insert_var(
            name.clone(),
            ValueWithType {
                value: Value::NativeFunction { name, func },
                type_,
            },
        );
    }

    pub fn insert_variable_as_symbol(&mut self, name: SymbolValue) {
        self.insert_var(name.clone(), Value::Symbol(name).with_type());
    }
}

/// Reference of Local. `None` represents the root.
pub type LocalRef<T> = Option<Rc<RefCell<Local<T>>>>;

/// A Local has mappings for local variables.
///
/// The Environment has a local as currently evaluation.
/// A lambda also has a local to realize closures.
///
/// Locals chains like this.
///
/// ```text
/// Environment.head_local -> local1 -> local2 ... -> None (root)
/// ```
#[derive(PartialEq, Debug)]
pub struct Local<T> {
    variables: FxHashMap<u32, T>,
    parent: LocalRef<T>,
}

impl<T> Local<T>
where
    T: Clone + std::fmt::Debug,
{
    fn new(parent: LocalRef<T>) -> Local<T> {
        Local {
            variables: HashMap::default(),
            parent,
        }
    }

    pub fn find_var(&mut self, id: u32) -> Option<T> {
        if let Some(value) = self.variables.get(&id) {
            Some(value.clone())
        } else if let Some(parent) = &self.parent {
            parent.borrow_mut().find_var(id)
        } else {
            None
        }
    }

    pub fn update_var(&mut self, id: u32, value: &T) -> bool {
        if let Some(_) = self.variables.get(&id) {
            self.variables.insert(id, value.clone());
            true
        } else if let Some(parent) = &self.parent {
            parent.borrow_mut().update_var(id, value)
        } else {
            false
        }
    }

    fn dump(&self) {
        if let Some(parent) = &self.parent {
            // Don't print root local.
            printlnuw(&format!("{:#?}", self.variables));
            parent.borrow_mut().dump()
        }
    }
}
