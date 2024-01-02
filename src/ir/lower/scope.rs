use std::collections::HashMap;

use crate::ir::{Var, Value};

pub struct LoopScope {
    /// output variable if the loop is used in an expression
    pub output_var: Option<Var>,
    // TODO
    // allows for breaking out of a specific loop
    // still figuring out the syntax and implementation
    // pub label: Option<Label>
}

pub struct Scopes<'a> {
    /// stack of defined variable scopes (blocks)
    variable_scopes: Vec<HashMap<&'a str, Var>>,
    /// stack of shorthands used in pipelines
    shorthands: Vec<Value>,
    /// stack of the loops we are in
    loop_scopes: Vec<LoopScope>
}

impl<'a> Scopes<'a> {
    /// initializes a `Scopes` object with one variable scope already pushed
    pub fn new() -> Self {
        Self { 
            variable_scopes: vec![Default::default()],
            shorthands: vec![],
            loop_scopes: vec![]
        }
    }

    pub fn var(&self, name: &str) -> Option<Var> {
        self.variable_scopes.iter().rev().find_map(|s| s.get(name).copied())
    }

    pub fn add_var(&mut self, name: &'a str, var: Var) {
        if let Some(s) = self.variable_scopes.last_mut() {
            s.insert(name, var);
        }
    }

    /// add a new scope (when starting a block)
    pub fn push(&mut self) {
        self.variable_scopes.push(Default::default());
    }

    /// remove a scope (when leaving a block)
    pub fn pop(&mut self) {
        self.variable_scopes.pop();
    }

    /// add a shorthand (entering pipeline expression)
    pub fn push_shorthand(&mut self, var: Value) {
        self.shorthands.push(var);
    }

    /// remove a shorthand (leaving pipeline expression)
    pub fn pop_shorthand(&mut self) {
        self.shorthands.pop();
    }

    /// get the current shorthand
    pub fn shorthand(&self) -> Option<Value> {
        self.shorthands.last().copied()
    }

    /// enter a loop
    pub fn push_loop(&mut self, l: LoopScope) {
        self.loop_scopes.push(l);
    }

    /// leave a loop
    pub fn pop_loop(&mut self) {
        self.loop_scopes.pop();
    }

    pub fn current_loop(&self) -> Option<&LoopScope> {
        self.loop_scopes.last()
    }
}
