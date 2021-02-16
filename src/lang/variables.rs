use std::collections::BTreeMap;

use crate::lang::ast::Identifier;

pub struct Variables<T> {
    inner: Vec<BTreeMap<Identifier, T>>,
}

impl<T> Variables<T> {
    pub fn new() -> Self {
        Variables {
            inner: vec![BTreeMap::default()],
        }
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
