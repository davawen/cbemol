use super::*;

pub struct Error(pub String);

impl Error {
    fn new(msg: impl Into<String>) -> Self {
        Error(msg.into())
    }

    fn errs<T>(self) -> Result<T> {
        Err(vec![self])
    }
}

type Result<T> = std::result::Result<T, Vec<Error>>;

// TODO: keep track of initialized and moved variables

impl Program<'_> {
    /// this method will fill out the type of undeclared variable (created during lowering),
    /// and check that the types specified everywhere in the program match up correctly
    pub fn typecheck(&mut self) -> Vec<Error> {
        let mut errs = vec![];
        for (_, decl) in &mut self.function_decls {
            take_mut::take(&mut decl.ret, |ret| ret.flatten(&self.types));
            for param in &mut decl.params {
                take_mut::take(&mut param.ty, |ty| ty.flatten(&self.types));
            }
        }

        for (key, func) in &mut self.functions {
            for (_, var) in &mut func.variables {
                take_mut::take(&mut var.ty, |ty| ty.flatten(&self.types));
            }
            
            errs.extend(func.body.typecheck(&mut State {
                types: &self.types,
                decls: &self.function_decls,
                decl: &self.function_decls[key],
                vars: &mut func.variables
            }));
        }
        errs
    }
}

type Types<'a> = SlotMap<TypeKey, DirectType<'a>>;
struct State<'a, 'b> {
    /// all the types known in the program
    types: &'b Types<'a>,
    /// the declaration of all functions
    decls: &'b SecondaryMap<FuncKey, FunctionDecl<'a>>,
    /// the declaration of the currently checked function
    decl: &'b FunctionDecl<'a>,
    /// the variables of the currently checked function
    vars: &'b mut SlotMap<Var, Variable> 
}

impl<'a> Block<'a> {
    fn typecheck<'b, 'c>(&'b mut self, state: &'c mut State<'a, 'b>) -> Vec<Error> {
        let mut errs = vec![];
        for stmt in &mut self.stmts {
            match stmt {
                Statement::Assign(var, expr) => {
                    let expr = match expr.typecheck(state) {
                        Ok(expr) => expr,
                        Err(e) => {
                            errs.extend(e);
                            continue;
                        }
                    };

                    let var = &mut state.vars[*var];
                    if let Type::Undeclared = &var.ty {
                        var.ty = expr;
                    } else if !var.ty.same_as(&expr) {
                        errs.push(Error::new(format!("expected type {}, found {}", var.ty, expr)));
                    }
                }
                Statement::DerefAssign(value, expr) => {
                    let expr = expr.typecheck(state);
                    let value = value.typecheck(state);
                    match (expr, value) {
                        (Ok(expr), Ok(value)) => if !expr.same_as(&value) {
                            errs.push(Error::new(format!("expected type {value}, found {expr}")));
                        }
                        (expr, value) => {
                            if let Err(e) = expr  { errs.extend(e) }
                            if let Err(e) = value { errs.extend(e) }
                        }
                    }
                },
                Statement::Do(expr) => if let Err(e) = expr.typecheck(state) {
                    errs.extend(e);
                },
                Statement::Block(block) => errs.extend(block.typecheck(state)),
                Statement::If { cond, block, else_block } => {
                    match cond.typecheck(state) {
                        Ok(Type::Primitive(PrimitiveType::Bool)) => (),
                        Ok(ty) => errs.push(Error::new(format!("expected a boolean in condition of if statement, got {ty}"))),
                        Err(e) => errs.extend(e)
                    }
                    errs.extend(block.typecheck(state));
                    if let Some(else_block) = else_block {
                        errs.extend(else_block.typecheck(state));
                    }
                },
                Statement::Loop(block) => errs.extend(block.typecheck(state)),
            }
        }
        errs
    }
}

impl<'a> Expr<'a> {
    fn typecheck<'b, 'c>(&'b mut self, state: &'c mut State<'a, 'b>) -> Result<Type> {
        let ty = match self {
            Expr::Value(v) => v.typecheck(state)?,
            Expr::FieldAccess(value, field) => {
                match value.typecheck(state)? {
                    Type::Direct(key) if matches!(state.types[key], DirectType::Struct { .. }) => {
                        let DirectType::Struct { fields } = &state.types[key] else { unreachable!() };
                        if let Some((_, field)) = fields.iter().find(|(name, ty)| name == field) {
                            field.clone()
                        } else {
                            return Error::new(format!("field {field} does not exist on struct")).errs();
                        }
                    }
                    _ => return Error::new("accessing a field on a variable that is not a struct").errs()
                }
            },
            Expr::PathAccess(ty, _) => {
                match &state.types[*ty] {
                    DirectType::Enum { .. } => Type::Primitive(PrimitiveType::I32),
                    _ => unreachable!("should be checked during lowering")
                }
            },
            Expr::FuncCall(key, args) => {
                let decl = &state.decls[*key];
                if args.len() != decl.params.len() { unreachable!("should be checked during lowering") }
                for (param, arg) in decl.params.iter().zip(args) {
                    let arg = arg.typecheck(state)?;
                    if !arg.same_as(&param.ty) {
                        return Error::new(format!("wrong type in function call, expected {}, got {}", param.ty, arg)).errs()
                    }
                }
                decl.ret.clone()
            },
            Expr::Return(value) => {
                if let Some(value) = value {
                    let value = value.typecheck(state)?;
                    if !value.same_as(&state.decl.ret) {
                        return Error::new(format!("wrong type returned from function, expected {}, got {}", state.decl.ret, value)).errs()
                    }
                }
                Type::Never
            },
            Expr::Break => Type::Never,
            Expr::Continue => Type::Never,
            Expr::BinOp(a, op, b) => {
                let a = a.typecheck(state)?;
                let b = b.typecheck(state)?;
                use BinOp as O;
                match op {
                    O::Add | O::Sub => {
                        if (a.is_numeric() && b.is_numeric() && a.same_as(&b)) || (a.is_ptr() && b.is_numeric()) { a } 
                        else if a.is_numeric() && b.is_ptr() { b }
                        else {
                            return Error::new(format!("cannot add/substract types {a} and {b}")).errs()
                        }
                    }
                    O::Mul | O::Div | O::Mod => {
                        if a.is_numeric() && b.is_numeric() && a.same_as(&b) { a } 
                        else {
                            return Error::new(format!("cannot apply arithmetic operations on types {a} and {b}")).errs()
                        }
                    }
                    O::And | O::Or | O::Xor => {
                        if (a.is_numeric() && b.is_numeric() && a.same_as(&b)) || a.is_bool() && b.is_bool() { a }
                        else {
                            return Error::new(format!("cannot apply binary operations on types {a} and {b}")).errs()
                        }
                    }
                    O::LogicAnd | O::LogicOr | O::LogicXor => {
                        if a.is_bool() && b.is_bool() { a }
                        else {
                            return Error::new("can only apply logical operations on boolean types").errs()
                        }
                    }
                    O::Eq | O::Ne | O::Gt | O::Lt | O::Ge | O::Le => {
                        if a.same_as(&b) { Type::Primitive(PrimitiveType::Bool) }
                        else {
                            return Error::new("can only compare two types that are the same").errs()
                        }
                    }
                }
            },
            Expr::UnaryOp(op, value) => {
                let value = value.typecheck(state)?;
                use UnaryOp as O;
                match op {
                    O::Not => {
                        if value.is_bool() { value }
                        else {
                            return Error::new("can only invert a boolean value").errs()
                        }
                    }
                    O::Deref => {
                        match value {
                            Type::Ptr(value) => (*value).clone(),
                            _ => return Error::new("can only dereference pointers").errs()
                        }
                    }
                    O::Negate => {
                        if value.is_numeric() { value }
                        else {
                            return Error::new("can only negate numbers").errs()
                        }
                    }
                    O::AddressOf => {
                        Type::Ptr(Box::new(value))
                    }
                }
            },
        };
        Ok(ty)
    }
}

impl Value {
    fn typecheck<'b>(&'b self, state: &mut State<'_, 'b>) -> Result<Type> {
        let ty = match self {
            &Value::Var(v) => match state.vars[v].ty.clone() {
                Type::Undeclared => return Error::new("cannot use variable whose type is undeclared").errs(),
                ty => ty
            },
            Value::Num(_) => Type::Primitive(PrimitiveType::I32),
            Value::Literal(_) => Type::Ptr(Box::new(Type::Primitive(PrimitiveType::U8))),
            Value::Uninit => Type::Uninit,
            Value::Unit => Type::Unit,
        };
        Ok(ty)
    }
}

impl Type {
    /// flattens Type::Direct's that point to DirectType::Type
    fn flatten<'b>(self, types: &'b Types<'_>) -> Self {
        match self {
            Type::Direct(key) => if let DirectType::Type(ty) = &types[key] {
                ty.clone().flatten(types)
            } else { Type::Direct(key) }
            Type::Ptr(ty) => Type::Ptr(Box::new(ty.flatten(types))),
            Type::Slice(ty) => Type::Slice(Box::new(ty.flatten(types))),
            Type::Array { ty, len } => Type::Array { ty: Box::new(ty.flatten(types)), len },
            Type::Func { ret, params } => Type::Func {
                ret: Box::new(ret.flatten(types)),
                params: params.into_iter().map(|p| p.flatten(types)).collect()
            },
            _ => self
        }
    }

    fn is_numeric<'b>(&self) -> bool {
        use PrimitiveType as P;
        match self {
            Type::Primitive(p) => matches!(p, P::U8 | P::I32 | P::F32),
            _ => false
        }
    }

    fn is_ptr<'b>(&self) -> bool {
        matches!(self, Type::Ptr(_))
    }

    fn is_bool(&self) -> bool {
        matches!(self, Type::Primitive(PrimitiveType::Bool))
    }

    fn same_as<'b>(&'b self, other: &'b Self) -> bool {
        match (self, other) {
            (Type::Never, _) | (_, Type::Never) => true,
            (Type::Uninit, _) | (_, Type::Uninit) => true,
            (Type::Unit, Type::Unit) => true,
            (Type::Undeclared, _) | (_, Type::Undeclared) => false,
            (Type::Direct(k1), Type::Direct(k2)) => k1 == k2,
            (Type::Primitive(p1), Type::Primitive(p2)) => p1 == p2,
            (Type::Ptr(p1), Type::Ptr(p2)) => p1.same_as(p2),
            (Type::Slice(t1), Type::Slice(t2)) => t1.same_as(t2),
            (Type::Array { ty: t1, len: l1 }, Type::Array { ty: t2, len: l2 }) => l1 == l2 && t1.same_as(t2),
            (Type::Func { ret: r1, params: p1 }, Type::Func { ret: r2, params: p2 }) => 
                p1.len() == p2.len() && r1.same_as(r2) && !p1.iter().zip(p2.iter()).any(|(p1, p2)| !p1.same_as(p2)),
            _ => false
        }
    }
}
