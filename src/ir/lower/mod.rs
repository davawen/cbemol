use std::collections::VecDeque;

use crate::ast::{Ast, self, Span};

use self::scope::Scopes;

use super::*;

mod scope;

pub struct Error {
    pub message: String,
    pub label: Option<(Span, String)>
}

pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    fn new(message: impl ToString) -> Self {
        Self {
            message: message.to_string(),
            label: None
        }
    }

    fn with_label(mut self, span: Span, message: impl ToString) -> Self {
        self.label = Some((span, message.to_string()));
        self
    }
}

impl<'a> Program<'a> {
    pub fn lower(program: &'a [Ast<'a>]) -> Result<Self> {
        let mut this = Self::default();

        this.parse_type_decls(program)?;
        this.parse_types_and_func_decls(program)?;
        this.parse_funcs(program)?;

        Ok(this)
    }

    fn parse_type_decls(&mut self, program: &[Ast<'a>]) -> Result<()> {
        self.type_decls.insert("void", self.types.insert(UserType::Unit));
        self.type_decls.insert("i32",  self.types.insert(UserType::Primitive(PrimitiveType::I32)));
        self.type_decls.insert("f32",  self.types.insert(UserType::Primitive(PrimitiveType::F32)));

        // parse types
        for decl in program {
            match decl {
                &Ast::StructDef { name, .. } | &Ast::UnionDef { name, .. } | &Ast::EnumDef { name, .. } => {
                    let handle = self.types.insert(UserType::Never); // placeholder
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
                    let ty = UserType::Struct {
                        fields: fields.iter().map(|(ty, name)| Ok((*name, self.parse_type(ty)?))).collect::<Result<_>>()?
                    };
                    self.types[self.type_decls[name]] = ty;
                }
                Ast::UnionDef { name, variants, span: _ } => {
                    let ty = UserType::Union {
                        variants: variants.iter().map(|(ty, name)| Ok((*name, self.parse_type(ty)?))).collect::<Result<_>>()?
                    };
                    self.types[self.type_decls[name]] = ty;
                }
                Ast::EnumDef { name, variants, span: _ } => {
                    let mut count = 0;
                    let ty = UserType::Enum {
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
                    let handle = self.functions.insert(Function::default());
                    self.function_decls.insert(name, FunctionDecl {
                        ret: self.parse_type(ret)?,
                        params: params.iter().map(|param| {
                            if let Some(value) = &param.value {
                                Err(Error::new("default values are not supported yet").with_label(value.span(), "used here"))?
                            }
                            Ok(Param {
                                name: param.name,
                                ty: self.parse_type(&param.ty)?,
                                outward_name: param.outward_name
                            })
                        }).collect::<Result<_>>()?,
                        key: handle
                    });
                }
                _ => ()
       }
        }
        Ok(())
    }

    fn parse_funcs(&mut self, program: &'a [Ast<'a>]) -> Result<()> {
        for decl in program {
            if let Ast::FunctionDef { name, body, span: _, .. } = decl {
                let decl = &self.function_decls[name];

                let mut func = Function::default();
                let mut scopes = Scopes::new();
                func.body = self.parse_func(body, decl, &mut func, &mut scopes)?;
                self.functions[decl.key] = func;
            }
        }

        Ok(())
    }

    fn parse_func<'b>(&self, body: &'a ast::Block<'a>, decl: &FunctionDecl<'a>, func: &'b mut Function<'a>, scopes: &'b mut Scopes<'a>) -> Result<Block<'a>> {
        scopes.push();
        for param in &decl.params {
            let var = func.variables.insert(Variable { ty: param.ty.clone() });
            scopes.add_var(param.name, var);
        }

        let mut env = Block::default();
        for statement in &body.0 {
            self.parse_statement(statement, func, &mut env, scopes)?;
        }

        if let Some(expr) = &body.1 {
            let tmp = self.parse_expr_into_tmp(expr, func, &mut env, scopes)?;
            env.stmts.push(Statement::Do(Expr::Return(Some(tmp))));
        }

        scopes.pop();
        Ok(env)
    }

    fn parse_statement<'b>(&'b self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<()> {
        match node {
            Ast::Declare { var, ty, value, span: _ } => {
                // evaluate value before adding the variable to scope
                let value = value.as_ref().map(|value| self.parse_expr(value, func, env, scopes));

                let ty = self.parse_type(ty)?;
                let key = func.variables.insert(Variable { ty });
                scopes.add_var(var, key);

                if let Some(value) = value {
                    env.stmts.push(Statement::Assign(key, value?));
                }
            }
            Ast::Assign { var, value, span } => {
                let value = self.parse_expr(value, func, env, scopes)?;

                let statement = match var {
                    ast::LValue::Id(name) => {
                        let var = scopes.var(name)
                            .ok_or(Error::new(format!("unknown variable {name}")).with_label(*span, "assigned to here"))?;
                        Statement::Assign(var, value)
                    }
                    ast::LValue::Deref(expr) => if let Ast::Id(name, span) = &**expr {
                        Statement::SetDeref(scopes.var(name)
                            .ok_or(Error::new(format!("unknown variable {name}")).with_label(*span, "used here"))?,
                            value
                        )
                    } else {
                        Statement::SetDeref(self.parse_expr_into_tmp(expr, func, env, scopes)?, value)
                    }
                    ast::LValue::Index(_array, _index) => Err(Error::new("TODO: implement indexing").with_label(*span, "used here"))?
                };
                env.stmts.push(statement);
            }
            Ast::Block(block, _span) => {
                let block = {
                    scopes.push();
                    let mut env = Block::default();
                    for statement in &block.0 {
                        self.parse_statement(statement, func, &mut env, scopes)?;
                    }

                    if let Some(expr) = &block.1 {
                        let expr = self.parse_expr(expr, func, &mut env, scopes)?;
                        env.stmts.push(Statement::Do(expr));
                    }
                    scopes.pop();
                    env
                };
                env.stmts.push(Statement::Block(block));
            }
            Ast::IfExpr { span, .. } | Ast::LoopExpr(_, span) | Ast::ForExpr { span, .. } => Err(
                Error::new("TODO: implement control flow").with_label(*span, "used here")
            )?,
            // Ast::IfExpr { cond, block, span } => todo!(),
            // Ast::LoopExpr(_, _) => todo!(),
            // Ast::ForExpr { decl, it, body, span } => todo!(),
            Ast::FunctionDef { span, .. } | Ast::StructDef { span, .. } | Ast::EnumDef { span, .. } | Ast::UnionDef { span, .. } => Err(
                Error::new("cannot define function or struct inside of body of another function")
                    .with_label(*span, "defined here")
            )?,
            node => {
                let expr = self.parse_expr(node, func, env, scopes)?;
                env.stmts.push(Statement::Do(expr));
            }
        }

        Ok(())
    }

    fn parse_expr<'b>(&self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<Expr<'a>> {
        let expr = match node {
            Ast::Id(name, span) => Expr::Var(scopes.var(name).ok_or(Error::new(format!("unknown variable {name}")).with_label(*span, "used here"))?),
            &Ast::Num(num, _) => Expr::Num(num),
            Ast::Literal(str, _) => Expr::Literal(str.clone()),
            Ast::Shorthand(span) => {
                Expr::Var(scopes.shorthand().ok_or(
                    Error::new("using a shorthand when not inside of a pipeline expression").with_label(*span, "appeared here")
                )?)
            }
            Ast::Uninit(_) => Expr::Uninit,
            Ast::UnaryExpr(op, expr, _) => {
                let expr = self.parse_expr_into_tmp(expr, func, env, scopes)?;
                // pretty stupid but future unary operations might need desugaring
                let op = match op {
                    ast::UnaryOp::Deref     => UnaryOp::Deref,
                    ast::UnaryOp::AddressOf => UnaryOp::AddressOf,
                    ast::UnaryOp::Negate    => UnaryOp::Negate,
                    ast::UnaryOp::Not       => UnaryOp::Not
                };
                Expr::UnaryOp(op, expr)
            }
            Ast::BinExpr(a, op, b, span) => match op {
                ast::BinOp::Range => Err(
                    Error::new("TODO: range struct and range syntax").with_label(*span, "used here")
                )?,
                ast::BinOp::Pipe => {
                    let a = self.parse_expr_into_tmp(a, func, env, scopes)?;
                    scopes.push_shorthand(a);

                    let b = self.parse_expr(b, func, env, scopes)?;
                    scopes.pop_shorthand();
                    b
                }
                op => {
                    let a = self.parse_expr_into_tmp(a, func, env, scopes)?;
                    let b = self.parse_expr_into_tmp(b, func, env, scopes)?;
                    let op = match op {
                        ast::BinOp::Add    => BinOp::Add,
                        ast::BinOp::Sub    => BinOp::Sub,
                        ast::BinOp::Mul    => BinOp::Mul,
                        ast::BinOp::Div    => BinOp::Div,
                        ast::BinOp::Mod    => todo!(),
                        ast::BinOp::BinAnd => todo!(),
                        ast::BinOp::BinOr  => todo!(),
                        ast::BinOp::BinXor => todo!(),
                        ast::BinOp::And    => todo!(),
                        ast::BinOp::Or     => todo!(),
                        ast::BinOp::Xor    => todo!(),
                        ast::BinOp::Eq     => todo!(),
                        ast::BinOp::Ne     => todo!(),
                        ast::BinOp::Gt     => todo!(),
                        ast::BinOp::Ge     => todo!(),
                        ast::BinOp::Lt     => todo!(),
                        ast::BinOp::Le     => todo!(),
                        ast::BinOp::Range  => unreachable!(),
                        ast::BinOp::Pipe   => unreachable!(),
                    };
                    Expr::BinOp(a, op, b)
                }
            },
            Ast::Access(a, field, span) => {
                if let Ast::Id(var, _) = &**a {
                    if let Some(var) = scopes.var(var) { // acessing local variable
                        Expr::FieldAccess(var, field)
                    } else { // acessing type constant
                        let ty = self.type_decls.get(var).copied().ok_or(Error::new(format!("variable/type not declared: {var}")).with_label(*span, "used here"))?;
                        match &self.types[ty] {
                            UserType::Enum { variants } => if !variants.iter().any(|(name, _)| name == field) {
                                Err(Error::new(format!("enumeration does not contain member {field}")).with_label(*span, "accessed here"))?
                            }
                            _ => Err(Error::new(format!("cannot access member of type {var}")).with_label(*span, "accessed here"))?
                        }
                        Expr::PathAccess(ty, field)
                    }
                } else {
                    let var = self.parse_expr_into_tmp(a, func, env, scopes)?;
                    Expr::FieldAccess(var, field)
                }
            },
            // TODO: keep additional information in scope about which loop it comes from
            Ast::Break(expr, _) => Expr::Break(expr.as_ref().map(|e| self.parse_expr_into_tmp(e, func, env, scopes)).transpose()?),
            Ast::Continue(expr, _) => Expr::Continue(expr.as_ref().map(|e| self.parse_expr_into_tmp(e, func, env, scopes)).transpose()?),
            Ast::Block(block, span) => {
                // store bock return value
                let v = func.variables.insert(Variable { ty: Type::Undeclared });

                scopes.push();
                let mut env = Block::default();
                for statement in &block.0 {
                    self.parse_statement(statement, func, &mut env, scopes)?;
                }

                if let Some(expr) = &block.1 {
                    let expr = self.parse_expr(expr, func, &mut env, scopes)?;
                    env.stmts.push(Statement::Assign(v, expr));
                } else {
                    Err(Error::new("block is expected to return a value, but doesn't have any end expression").with_label(*span, "defined here"))?
                }

                scopes.pop();
                Expr::Var(v)
            },
            Ast::FuncCall { name, args, span } => {
                let decl = self.function_decls.get(name).ok_or(
                    Error::new(format!("unknown function {name}")).with_label(*span, "called here")
                )?;

                // make sure args are processed in the same order they are specified
                let mut args: VecDeque<_> = args.iter().map(|(name, expr)| Ok((name, self.parse_expr_into_tmp(expr, func, env, scopes)?))).collect::<Result<_>>()?;
                let mut ordered_args = Vec::new();

                let num_args = args.len();

                for param in &decl.params {
                    if let Some(outward_name) = &param.outward_name { // named parameter
                        let arg = args.iter().position(|(name, _)| **name == Some(outward_name)).ok_or(
                            Error::new(format!("expected argument {outward_name} in function call")).with_label(*span, "called here")
                        )?;
                        ordered_args.push(args.remove(arg).unwrap().1);
                    } else { // positional parameter
                        let arg = args.pop_front().ok_or(
                            Error::new(format!("not enough arguments given, expected {}, got {num_args}", decl.params.len())).with_label(*span, "called here")
                        )?;
                        ordered_args.push(arg.1);
                    }

                    // TODO: default values
                    // TODO: in error message, add label to the function definition
                }

                if !args.is_empty() {
                    for arg in &args {
                        if let Some(name) = arg.0 {
                            Err(Error::new(format!("unknown named argument given: {name}"))
                                .with_label(*span, "called here"))?
                        }
                    }

                    Err(Error::new(format!("too many arguments given, expected {}, got {num_args}", decl.params.len()))
                        .with_label(*span, "called here"))?
                }

                Expr::FuncCall(decl.key, ordered_args)
            },
            Ast::IfExpr { span, .. } | Ast::LoopExpr(_, span) | Ast::ForExpr { span, .. } => Err(
                Error::new("TODO: implement expression control flow (store resulting block expression into variable in outer scope)")
                    .with_label(*span, "used here")
            )?,
            Ast::Declare { span, .. } | Ast::Assign { span, .. } => Err(
                Error::new("variable assignment and declaration does not yield a value and cannot be used as an expression")
                    .with_label(*span, "used here as an expression")
            )?,
            Ast::FunctionDef { span, .. } | Ast::StructDef { span, .. } | Ast::EnumDef { span, .. } | Ast::UnionDef { span, .. } => Err(
                Error::new("cannot define function or struct inside of body of another function")
                    .with_label(*span, "defined here")
            )?,
        };

        Ok(expr)
    }

    fn parse_expr_into_tmp<'b>(&self, node: &'a Ast<'a>, func: &'b mut Function<'a>, env: &'b mut Block<'a>, scopes: &'b mut Scopes<'a>) -> Result<Var> {
        let expr = self.parse_expr(node, func, env, scopes)?;
        if let Expr::Var(v) = expr { return Ok(v) } // avoid unnecessary temporary

        let var = func.variables.insert(Variable { ty: Type::Undeclared });
        env.stmts.push(Statement::Assign(var, expr));
        Ok(var)
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
