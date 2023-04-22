use rustc_hash::FxHashMap;
use std::{
    cell::{Ref, RefCell},
    collections::HashMap,
    rc::Rc,
};

use super::{console::*, error::*, SymbolValue};

pub struct Environment<T> {
    pub head_local: LocalRef<T>,
    /// For referencing variables from closure.
    pub lambda_local: LocalRef<T>,
}

impl<T> Environment<T>
where
    T: Clone,
{
    pub fn update_var(&mut self, name: SymbolValue, value: &T) -> Result<(), Error> {
        let mut local = self.head_local.as_mut().unwrap().borrow_mut();
        if local.update_var(name.clone(), value) {
            Ok(())
        } else {
            Err(Error::Eval(format!(
                "A variable `{}` is not defined.",
                name
            )))
        }
    }

    pub fn insert_var(&mut self, name: SymbolValue, value: T) {
        // local_stack must have least one local
        let mut local = self.head_local.as_ref().unwrap().borrow_mut();
        local.variables.insert(name, value);
    }

    pub fn current_local(&self) -> Ref<Local<T>> {
        self.head_local.as_ref().unwrap().borrow()
    }

    pub fn find_var(&mut self, name: &SymbolValue) -> Option<T> {
        self.head_local
            .as_mut()
            .unwrap()
            .borrow_mut()
            .find_var(name.to_owned())
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

impl<T> Default for Environment<T>
where
    T: Clone,
{
    fn default() -> Self {
        let mut env = Environment {
            head_local: None,
            lambda_local: None,
        };
        env.push_local();
        env
    }
}

impl<T> Environment<T>
where
    T: Clone + std::fmt::Debug,
{
    #[allow(dead_code)]
    pub fn dump_local(&self) {
        let local = self.head_local.as_ref().unwrap().borrow();
        printlnuw("--- Locals ---");
        local.dump();
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
    pub variables: FxHashMap<LocalKey, T>,
    parent: LocalRef<T>,
}
type LocalKey = String;

impl<T> Local<T>
where
    T: Clone,
{
    fn new(parent: LocalRef<T>) -> Local<T> {
        Local {
            variables: HashMap::default(),
            parent,
        }
    }

    pub fn find_var(&mut self, id: LocalKey) -> Option<T> {
        if let Some(value) = self.variables.get(&id) {
            Some(value.clone())
        } else if let Some(parent) = &self.parent {
            parent.borrow_mut().find_var(id)
        } else {
            None
        }
    }

    pub fn update_var(&mut self, id: LocalKey, value: &T) -> bool {
        if self.variables.get(&id).is_some() {
            self.variables.insert(id, value.clone());
            true
        } else if let Some(parent) = &self.parent {
            parent.borrow_mut().update_var(id, value)
        } else {
            false
        }
    }
}

impl<T> Local<T>
where
    T: Clone + std::fmt::Debug,
{
    fn dump(&self) {
        if let Some(parent) = &self.parent {
            // Don't print root local.
            printlnuw(&format!("{:#?}", self.variables));
            parent.borrow_mut().dump()
        }
    }
}
