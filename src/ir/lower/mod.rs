use std::collections::VecDeque;

use crate::{ast::{Ast, self, Span}, error::Error};

use self::scope::Scopes;

use super::*;

mod scope;

pub type Result<T> = std::result::Result<T, Error>;

impl<'a> Program<'a> {
    pub fn lower(program: &'a [Ast<'a>]) -> Result<Self> {
        let mut this = Self::default();

        this.parse_type_decls(program)?;
        this.parse_types_and_func_decls(program)?;
        this.parse_funcs(program)?;

        Ok(this)
    }

    fn parse_type_decls(&mut self, program: &[Ast<'a>]) -> Result<()> {
        self.type_decls.insert("void", self.types.insert(DirectType::Type(Type::Unit)));
        self.type_decls.insert("u8",  self.types.insert(DirectType::Type(Type::Primitive(PrimitiveType::U8))));
        self.type_decls.insert("i32",  self.types.insert(DirectType::Type(Type::Primitive(PrimitiveType::I32))));
        self.type_decls.insert("f32",  self.types.insert(DirectType::Type(Type::Primitive(PrimitiveType::F32))));
        self.type_decls.insert("bool", self.types.insert(DirectType::Type(Type::Primitive(PrimitiveType::Bool))));

        // parse types
        for decl in program {
            match decl {
                &Ast::StructDef { name, .. } | &Ast::UnionDef { name, .. } | &Ast::EnumDef { name, .. } => {
                    let handle = self.types.insert(DirectType::Type(Type::Undeclared)); // placeholder
                    self.type_decls.insert(name, handle);
                }
                _ => ()
            }
        }
        Ok(())
    }

    fn parse_types_and_func_decls(&mut self, program: &[Ast<'a>]) -> Result<()> {
        for decl in program {
            match decl {
                Ast::StructDef { name, fields, span: _ } => {
                    let ty = DirectType::Struct {
                        fields: fields.iter().map(|(ty, name)| Ok((*name, self.parse_type(ty)?))).collect::<Result<_>>()?
                    };
                    self.types[self.type_decls[name]] = ty;
                }
                Ast::UnionDef { name, variants, span: _ } => {
                    let ty = DirectType::Union {
                        variants: variants.iter().map(|(ty, name)| Ok((*name, self.parse_type(ty)?))).collect::<Result<_>>()?
                    };
                    self.types[self.type_decls[name]] = ty;
                }
                Ast::EnumDef { name, variants, span: _ } => {
                    let mut count = 0;
                    let ty = DirectType::Enum {
                        variants: variants.iter().map(|(name, value)| {
                            if let &Some(value) = value { count = value; }
                            let value = count;
                            count += 1;
                            (*name, value)
                        }).collect()
                    };
                    self.types[self.type_decls[name]] = ty;
                }
                Ast::FunctionDef { name, ret, params, body: _, span: _ } => {
                    let decl = FunctionDecl {
                        ret: self.parse_type(ret)?,
                        params: params.iter().map(|param| {
                            if let Some(value) = &param.value {
                                return Error::new("default values are not supported yet").with_label(value.span(), "used here").err()
                            }
                            Ok(Param {
                                name: param.name,
                                ty: self.parse_type(&param.ty)?,
                                outward_name: param.outward_name
                            })
                        }).collect::<Result<_>>()?,
                    };

                    let handle = self.functions.insert(Function::default());
                    self.function_decls.insert(handle, decl);
                    self.function_names.insert(name, handle);
                }
                _ => ()
       }
        }
        Ok(())
    }

    fn parse_funcs(&mut self, program: &'a [Ast<'a>]) -> Result<()> {
        for decl in program {
            if let Ast::FunctionDef { name, body, span: _, .. } = decl {
                let key = self.function_names[name];

                let mut func = Function::default();
                let mut scopes = Scopes::new();
                func.body = self.parse_func(key, body, &mut func, &mut scopes)?;

                self.functions[key] = func;
            }
        }

        Ok(())
    }

    fn parse_func<'b>(&mut self, key: FuncKey, body: &'a ast::Block<'a>, func: &'b mut Function<'a>, scopes: &'b mut Scopes<'a>) -> Result<Block<'a>> {
        scopes.push();
        for param in &self.function_decls[key].params {
            let var = func.variables.insert(Variable { ty: param.ty.clone() });
            scopes.add_var(param.name, var);
        }

        let mut env = Block::default();
        for statement in &body.0 {
            self.parse_statement(statement, func, &mut env, scopes)?;
        }

        if let Some(expr) = &body.1 {
            let span = expr.span();
            let tmp = self.parse_expr_into_value(expr, func, &mut env, scopes)?;
            env.stmts.push(Statement::Do(Expr::Return(Some(tmp), span)));
        }

        scopes.pop();
        Ok(env)
    }

    fn parse_statement<'b>(&mut self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<()> {
        match node {
            Ast::Declare { var, ty, value, span } => {
                // evaluate value before adding the variable to scope
                let value = value.as_ref().map(|value| self.parse_expr(value, func, env, scopes));

                let ty = self.parse_type(ty)?;
                let key = func.variables.insert(Variable { ty });
                scopes.add_var(var, key);

                if let Some(value) = value {
                    env.stmts.push(Statement::Assign(key, value?, *span));
                }
            }
            Ast::Assign { var, value, span } => {
                let value = self.parse_expr(value, func, env, scopes)?;

                let statement = match var {
                    ast::LValue::Id(name) => {
                        let var = scopes.var(name)
                            .ok_or(Error::new(format!("unknown variable {name}")).with_label(*span, "assigned to here"))?;
                        Statement::Assign(var, value, *span)
                    }
                    ast::LValue::Deref(expr) => Statement::DerefAssign(self.parse_expr_into_value(expr, func, env, scopes)?, value, *span),
                    ast::LValue::Index(_array, _index) => return Error::new("TODO: implement indexing").with_label(*span, "used here").err()
                };
                env.stmts.push(statement);
            }
            Ast::Block(block, span) => {
                let block = self.parse_block(block, func, scopes, |expr| Ok(expr.map(|(expr, _)| Statement::Do(expr))))?;
                env.stmts.push(Statement::Block(block, *span));
            }
            &Ast::IfExpr { ref cond, ref block, ref else_branch, span } => {
                let cond = self.parse_expr(cond, func, env, scopes)?;
                let block = self.parse_block(block, func, scopes, |expr| Ok(expr.map(|(expr, _)| Statement::Do(expr))))?;
                let else_block = else_branch.as_ref().map(|branch| match &**branch {
                    Ast::IfExpr { .. } => {
                        let mut block = Block::default();
                        self.parse_statement(branch, func, &mut block, scopes)?;
                        Ok(block)
                    }
                    Ast::Block(b, _) => self.parse_block(b, func, scopes, |expr| Ok(expr.map(|(expr, _)| Statement::Do(expr)))),
                    _ => unreachable!()
                }).transpose()?;

                env.stmts.push(Statement::If { cond, block, else_block, span })
            }
            &Ast::LoopExpr(ref block, span) => {
                scopes.push_loop(scope::LoopScope { output_var: None });
                let block = self.parse_block(block, func, scopes, |expr| Ok(expr.map(|(expr, _)| Statement::Do(expr))))?;
                scopes.pop_loop();

                env.stmts.push(Statement::Loop(block, span))
            }
            Ast::ForExpr { span, .. } => return 
                Error::new("TODO: for expressions require implementation of interfaces and iterators")
                    .with_label(*span, "used here").err(),
            Ast::FunctionDef { span, .. } | Ast::StructDef { span, .. } | Ast::EnumDef { span, .. } | Ast::UnionDef { span, .. } => return 
                Error::new("cannot define function or struct inside of body of another function")
                    .with_label(*span, "defined here").err(),
            node => {
                let expr = self.parse_expr(node, func, env, scopes)?;
                env.stmts.push(Statement::Do(expr));
            }
        }

        Ok(())
    }

    fn parse_expr<'b>(&mut self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<Expr<'a>> {
        let expr = match node {
            Ast::Id(..) | Ast::Num(..) | Ast::Literal(..) | Ast::Shorthand(..) | Ast::Uninit(..) => {
                Expr::Value(self.parse_expr_into_value(node, func, env, scopes)?)
            }
            &Ast::UnaryExpr(ref op, ref expr, span) => {
                let expr = self.parse_expr_into_value(expr, func, env, scopes)?;
                // pretty stupid but future unary operations might need desugaring
                let op = match op {
                    ast::UnaryOp::Deref     => UnaryOp::Deref,
                    ast::UnaryOp::AddressOf => UnaryOp::AddressOf,
                    ast::UnaryOp::Negate    => UnaryOp::Negate,
                    ast::UnaryOp::Not       => UnaryOp::Not
                };
                Expr::UnaryOp(op, expr, span)
            }
            &Ast::BinExpr(ref a, ref op, ref b, span) => match op {
                ast::BinOp::Range => return Error::new("TODO: range struct and range syntax").with_label(span, "used here").err(),
                ast::BinOp::Pipe => {
                    let a = self.parse_expr_into_value(a, func, env, scopes)?;
                    scopes.push_shorthand(a);

                    let b = self.parse_expr(b, func, env, scopes)?;
                    scopes.pop_shorthand();
                    b
                }
                op => {
                    let a = self.parse_expr_into_value(a, func, env, scopes)?;
                    let b = self.parse_expr_into_value(b, func, env, scopes)?;
                    macro_rules! map_op {
                        ($op:expr, $($name:ident),* ; $($unreach:ident),*) => {
                            match $op {
                                $(ast::BinOp::$name => BinOp::$name),*,
                                $(ast::BinOp::$unreach => unreachable!()),*
                            }
                        };
                    }
                    let op = map_op! { op, 
                        Add, Sub, Mul, Div, Mod,
                        LogicAnd, LogicOr, LogicXor,
                        And, Or, Xor,
                        Eq, Ne, Gt, Ge, Lt, Le;
                        Range,
                        Pipe
                    };
                    Expr::BinOp(a, op, b, span)
                }
            },
            &Ast::Access(ref a, ref field, span) => {
                if let Ast::Id(var, var_span) = &**a {
                    if let Some(var) = scopes.var(var) { // acessing local variable
                        Expr::FieldAccess(Value::Var(var, *var_span), field, span)
                    } else { // acessing type constant
                        let ty = self.type_decls.get(var).copied().ok_or(Error::new(format!("variable/type not declared: {var}")).with_label(span, "used here"))?;
                        match &self.types[ty] {
                            DirectType::Enum { variants } => if !variants.iter().any(|(name, _)| name == field) {
                                return Error::new(format!("enumeration does not contain member {field}")).with_label(span, "accessed here").err()
                            }
                            _ => return Error::new(format!("cannot access member of type {var}")).with_label(span, "accessed here").err()
                        }
                        Expr::PathAccess(ty, field, span)
                    }
                } else {
                    let var = self.parse_expr_into_value(a, func, env, scopes)?;
                    Expr::FieldAccess(var, field, span)
                }
            },
            &Ast::Block(ref block, span) => {
                // store bock return value
                let v = func.variables.insert(Variable { ty: Type::Undeclared });
                let block = self.parse_block(block, func, scopes, 
                    |expr| Ok(expr.map(|(expr, span)| Statement::Assign(v, expr, span))
                        .or(Some(Statement::Assign(v, Value::Unit(span).expr(), span)))
                    )
                )?;
                env.stmts.push(Statement::Block(block, span));

                Value::Var(v, span).expr()
            },
            &Ast::FuncCall { ref name, ref args, span } => {
                // make sure args are processed in the same order they are specified
                let mut args: VecDeque<_> = args.iter().map(|(name, expr, span)| Ok((name, self.parse_expr_into_value(expr, func, env, scopes)?, *span))).collect::<Result<_>>()?;
                let mut ordered_args = Vec::new();

                let key = *self.function_names.get(name).ok_or(
                    Error::new(format!("unknown function {name}")).with_label(span, "called here")
                )?;
                let decl = &self.function_decls[key];

                let num_args = args.len();

                for param in &decl.params {
                    if let Some(outward_name) = &param.outward_name { // named parameter
                        let arg = args.iter().position(|(name, _, _)| **name == Some(outward_name)).ok_or(
                            Error::new(format!("expected argument {outward_name} in function call")).with_label(span, "called here")
                        )?;
                        ordered_args.push(args.remove(arg).unwrap().1);
                    } else { // positional parameter
                        let arg = args.pop_front().ok_or(
                            Error::new(format!("not enough arguments given, expected {}, got {num_args}", decl.params.len())).with_label(span, "called here")
                        )?;
                        ordered_args.push(arg.1);
                    }

                    // TODO: default values
                    // TODO: in error message, add label to the function definition
                }

                if !args.is_empty() {
                    for arg in &args {
                        if let Some(name) = arg.0 {
                            return Error::new(format!("unknown named argument given: {name}"))
                                .with_label(arg.2, "given here").err()
                        }
                    }

                    // remaining arguments are all positional
                    let span = args.iter().fold(args[0].2, |acc, (_, _, span)| Span::new(acc.start, span.end));

                    return Error::new(format!("too many arguments given, expected {}, got {num_args}", decl.params.len()))
                        .with_label(span, "given here").err()
                }

                Expr::FuncCall(key, ordered_args, span)
            },
            &Ast::IfExpr { ref cond, ref block, ref else_branch, span } => {
                // store return value
                let v = func.variables.insert(Variable { ty: Type::Undeclared });

                let last_map = |expr: Option<(Expr<'a>, Span)>| Ok(
                    expr.map(|(expr, span)| Statement::Assign(v, expr, span))
                        .or(Some(Statement::Assign(v, Value::Unit(span).expr(), span)))
                );

                let cond = self.parse_expr(cond, func, env, scopes)?;
                let block = self.parse_block(block, func, scopes, last_map)?;
                let Some(branch) = else_branch else {
                    return Error::new("no else branch after if expression")
                        .with_label(Span::new(span.end - 1, span.end), "expected else branch here").err()
                };

                let else_block = match &**branch {
                    &Ast::IfExpr { span, .. } => {
                        // FIXME: This recursively parses else-ifs as expression,
                        // which leads to the creation of many unneeded temporaries
                        // (the result of every else-if can and should directly be stored in `v`).
                        // It can be fixed by storing else-ifs linearly (as a vector),
                        // or by creating a special enum and function for parsing if blocks
                        let mut block = Block::default();
                        let ret = self.parse_expr(branch, func, &mut block, scopes)?;
                        block.stmts.push(Statement::Assign(v, ret, span));
                        block
                    }
                    Ast::Block(b, _) => self.parse_block(b, func, scopes, last_map)?,
                    _ => unreachable!()
                };
                env.stmts.push(Statement::If { cond, block, else_block: Some(else_block), span });
                Value::Var(v, span).expr()
            }
            &Ast::LoopExpr(ref block, span) => {
                // store return value
                let v = func.variables.insert(Variable { ty: Type::Undeclared });

                scopes.push_loop(scope::LoopScope { output_var: Some(v) });
                let block = self.parse_block(block, func, scopes, |expr| Ok(expr.map(|(expr, span)| Statement::Assign(v, expr, span))))?;
                scopes.pop_loop();

                env.stmts.push(Statement::Loop(block, span));
                Value::Var(v, span).expr()
            }
            &Ast::Break(ref expr, span) => {
                let expr = expr.as_ref().map(|expr| self.parse_expr(expr, func, env, scopes)).transpose()?;
                let Some(current_loop) = scopes.current_loop() else {
                    return Error::new("breaking when not inside of a loop")
                        .with_label(span, "break is here").err()
                };

                match (expr, current_loop.output_var) {
                    (None, None) | (None, Some(_)) => (),
                    (Some(_), None) => return Error::new("breaking with a value, inside of a loop that doesn't return anything")
                        .with_label(span, "break is here").err(),
                    (Some(expr), Some(var)) => env.stmts.push(Statement::Assign(var, expr, span))
                }
                Expr::Break(span)
            }
            &Ast::Continue(ref expr, span) => {
                let expr = expr.as_ref().map(|expr| self.parse_expr(expr, func, env, scopes)).transpose()?;
                let Some(current_loop) = scopes.current_loop() else {
                    return Error::new("continuing when not inside of a loop")
                        .with_label(span, "continue is here").err()
                };

                match (expr, current_loop.output_var) {
                    (None, None) | (None, Some(_)) => (),
                    (Some(_), None) => return Error::new("continuing with a value, inside of a loop that doesn't return anything")
                        .with_label(span, "continue is here").err(),
                    (Some(expr), Some(var)) => env.stmts.push(Statement::Assign(var, expr, span))
                }
                Expr::Continue(span)
            }
            Ast::ForExpr { span, .. } => return
                Error::new("for loops cannot return values (as there is a possibility they might never enter the loop)")
                    .with_label(*span, "used here").err(),
            Ast::Declare { span, .. } | Ast::Assign { span, .. } => return 
                Error::new("variable assignment and declaration does not yield a value and cannot be used as an expression")
                    .with_label(*span, "used here as an expression").err(),
            Ast::FunctionDef { span, .. } | Ast::StructDef { span, .. } | Ast::EnumDef { span, .. } | Ast::UnionDef { span, .. } => return 
                Error::new("cannot define function or struct inside of body of another function")
                    .with_label(*span, "defined here").err(),
        };

        Ok(expr)
    }

    fn parse_expr_into_value<'b>(&mut self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<Value> {
        let value = match node {
            &Ast::Id(name, span) => Value::Var(scopes.var(name).ok_or(Error::new(format!("unknown variable {name}")).with_label(span, "used here"))?, span),
            &Ast::Num(num, span) => Value::Num(num, span),
            &Ast::Literal(ref str, span) => Value::Literal(self.literals.insert(str.clone()), span),
            &Ast::Shorthand(span) => {
                scopes.shorthand().ok_or(
                    Error::new("using a shorthand when not inside of a pipeline expression").with_label(span, "appeared here")
                )?.with_span(span)
            }
            &Ast::Uninit(span) => Value::Uninit(span),
            node => {
                let expr = self.parse_expr(node, func, env, scopes)?;
                if let Expr::Value(value) = expr { return Ok(value) } // avoid unnecessary temporary

                let var = func.variables.insert(Variable { ty: Type::Undeclared });
                env.stmts.push(Statement::Assign(var, expr, node.span()));
                Value::Var(var, node.span())
            }
        };
        Ok(value)
    }

    /// parses a block
    /// handles pushing a new scope and adding every statement in the block
    /// doesn't require a reference to the current environment (since it creates one by itself)
    /// `last_map` specifies what to do with the last expression in the block
    fn parse_block<'b>(
        &mut self,
        block: &'a ast::Block<'a>,
        func: &'b mut Function<'a>,
        scopes: &'b mut Scopes<'a>,
        last_map: impl Fn(Option<(Expr<'a>, Span)>) -> Result<Option<Statement<'a>>>
    ) -> Result<Block<'a>> {
        scopes.push();
        let mut env = Block::default();
        for statement in &block.0 {
            self.parse_statement(statement, func, &mut env, scopes)?;
        }

        let last_expr = block.1.as_ref()
            .map(|expr| Ok((self.parse_expr(expr, func, &mut env, scopes)?, expr.span())))
            .transpose()?;

        if let Some(stmt) = last_map(last_expr)? {
            env.stmts.push(stmt);
        }
        scopes.pop();
        Ok(env)
    }

    fn parse_type(&self, ty: &ast::Type) -> Result<Type> {
        let ty = match ty {
            ast::Type::Id(id, span) => Type::Direct(self.type_decls.get(id).copied()
                .ok_or(Error::new(format!("unknown type {id}")).with_label(*span, "used here"))?
            ),
            ast::Type::Slice(ty, _) => Type::Slice(Box::new(self.parse_type(ty)?)),
            &ast::Type::Array { ref ty, len, .. } => Type::Array { ty: Box::new(self.parse_type(ty)?), len },
            ast::Type::Pointer(ty, _) => Type::Ptr(Box::new(self.parse_type(ty)?)),
            ast::Type::FunctionPointer { ret, args, .. } => Type::Func {
                ret: Box::new(self.parse_type(ret)?),
                params: args.iter().map(|ty| self.parse_type(ty)).collect::<Result<_>>()?
            }
        };
        Ok(ty)
    }
}
