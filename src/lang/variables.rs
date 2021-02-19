use std::collections::BTreeMap;

use crate::btrfs::definitions::CONSTANTS;
use crate::lang::{
    ast::Identifier,
    functions::{Function, FUNCTIONS},
};

pub struct Variables<T> {
    inner: Vec<BTreeMap<Identifier, T>>,
}

impl<T> Variables<T> {
    pub fn new(
        constant_constructor: fn(i128) -> T,
        function_constructor: fn(Function) -> T,
    ) -> Self {
        let mut map = BTreeMap::default();

        for constant in &*CONSTANTS {
            map.insert(
                Identifier(constant.name.to_string()),
                constant_constructor(constant.value),
            );
        }

        for func in &*FUNCTIONS {
            map.insert(Identifier(func.to_string()), function_constructor(*func));
        }

        Variables { inner: vec![map] }
    }

    pub fn push_scope(&mut self) {
        self.inner.push(BTreeMap::default());
    }

    pub fn pop_scope(&mut self) {
        assert!(!self.inner.is_empty());
        self.inner.pop();
    }

    pub fn get(&self, ident: &Identifier) -> Option<&T> {
        for scope in self.inner.iter().rev() {
            if let Some(ty) = scope.get(ident) {
                return Some(ty);
            }
        }

        None
    }

    pub fn insert(&mut self, ident: Identifier, val: T) {
        assert!(!self.inner.is_empty());
        self.inner.last_mut().unwrap().insert(ident, val);
    }
}
