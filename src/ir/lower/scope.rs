use std::collections::HashMap;

use crate::ir::{Var, Expr};

#[derive(Default)]
struct Scope<'a> {
    variables: HashMap<&'a str, Var>
}

pub struct Scopes<'a> {
    scopes: Vec<Scope<'a>>,
    /// stack of shorthands used in pipelines
    shorthands: Vec<Var>
}

impl<'a> Scopes<'a> {
    pub fn new() -> Self {
        Self { 
            scopes: vec![Scope::default()],
            shorthands: vec![]
        }
    }

    pub fn var(&self, name: &str) -> Option<Var> {
        self.scopes.iter().rev().find_map(|s| s.variables.get(name).copied())
    }

    pub fn add_var(&mut self, name: &'a str, var: Var) {
        if let Some(s) = self.scopes.last_mut() {
            s.variables.insert(name, var);
        }
    }

    /// add a new scope (when starting a block)
    pub fn push(&mut self) {
        self.scopes.push(Scope::default());
    }

    /// remove a scope (when leaving a block)
    pub fn pop(&mut self) {
        self.scopes.pop();
    }

    /// add a shorthand (right of pipeline expression)
    pub fn push_shorthand(&mut self, var: Var) {
        self.shorthands.push(var);
    }

    /// remove a shorthand (leaving pipeline expression)
    pub fn pop_shorthand(&mut self) {
        self.shorthands.pop();
    }

    /// get the current shorthand
    pub fn shorthand(&self) -> Option<Var> {
        self.shorthands.last().copied()
    }
}
