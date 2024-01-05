use std::fmt::Display;

use super::{Program, Block, Statement, Expr, UnaryOp, BinOp, Type, DirectType, PrimitiveType, Function, Value};

/// permits drilling the Program struct through the Display trait
struct WithProgram<'a, T>(&'a T, &'a Program<'a>);

trait DisplayProgram: Sized {
    fn with<'a>(&'a self, p: &'a Program) -> WithProgram<'a, Self> {
        WithProgram(self, p)
    }
}

impl<'a, T> DisplayProgram for T where WithProgram<'a, T>: Display + 'a {}

impl Display for Program<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (name, key) in &self.type_decls {
            let ty = &self.types[*key];
            writeln!(f, "{name} -> {key:?}: {ty}")?;
        }

        for (name, &key) in &self.function_names {
            let func = &self.functions[key];
            let decl = &self.function_decls[key];
            write!(f, "{} {name} (", decl.ret)?;
            for param in &decl.params {
                write!(f, "{}, ", param.ty)?;
            }
            writeln!(f, ") -> {:?}:\n{}", key, func.with(self))?;
        }

        Ok(())
    }
}

impl Display for DirectType<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use DirectType as Ty;
        match self {
            Ty::Type(ty) => write!(f, "{ty}"),
            Ty::Struct { fields } => {
                writeln!(f, "struct {{")?;
                for (field, ty) in fields {
                    writeln!(f, "  {field}: {ty}")?;
                }
                write!(f, "}}")
            }
            Ty::Union { variants } => {
                writeln!(f, "union {{")?;
                for (field, ty) in variants {
                    writeln!(f, "  {field}: {ty}")?;
                }
                write!(f, "}}")
            }
            Ty::Enum { variants } => {
                writeln!(f, "enum {{")?;
                for (name, value) in variants {
                    writeln!(f, "  {name} = {value}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type as Ty;
        match self {
            Ty::Undeclared => write!(f, "undeclared"),
            Ty::Direct(ty) => write!(f, "{ty:?}"),
            Ty::Ptr(ty) => write!(f, "{ty}&"),
            Ty::Array { ty, len } => write!(f, "{ty}[{len}]"),
            Ty::Slice(ty) => write!(f, "{ty}[]"),
            Ty::Unit => write!(f, "void"),
            Ty::Never => write!(f, "never"),
            Ty::Uninit => write!(f, "---"),
            Ty::Primitive(ty) => write!(f, "{ty}"),
            Ty::Func { ret, params } => {
                write!(f, "{ret}(")?;
                for param in params {
                    write!(f, "{param}, ")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use PrimitiveType as Ty;
        let s = match self {
            Ty::I32 => "i32",
            Ty::F32 => "f32",
            Ty::Bool => "bool",
            Ty::U8 => "u8"
        };
        write!(f, "{s}")
    }
}

impl Display for WithProgram<'_, Function<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for (key, var) in &self.0.variables {
            writeln!(s, "{key:?} -> {}", var.ty)?;
        }
        writeln!(s, "{}", self.0.body.with(self.1))?;
        for line in s.lines() {
            writeln!(f, "    {line}")?;
        }
        Ok(())
    }
}

impl Display for WithProgram<'_, Block<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for stmt in &self.0.stmts {
            write!(s, "{}", stmt.with(self.1))?;
        }

        writeln!(f, "{{")?;
        for line in s.lines() {
            writeln!(f, "    {line}")?;
        }
        write!(f, "}}")
    }
}

impl Display for WithProgram<'_, Statement<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Statement::Do(e) => writeln!(f, "DO {}", e.with(self.1)),
            Statement::Assign(var, e, _) => writeln!(f, "{var:?} = {}", e.with(self.1)),
            Statement::DerefAssign(var, e, _) => writeln!(f, "*{} = {}", var.with(self.1), e.with(self.1)),
            Statement::Block(b, _) => writeln!(f, "{}", b.with(self.1)),
            Statement::If { cond, block, else_block: Some(else_block), span: _ } => writeln!(f, "IF {} THEN {} ELSE {}", cond.with(self.1), block.with(self.1), else_block.with(self.1)),
            Statement::If { cond, block, else_block: None, span: _ } => writeln!(f, "IF {} THEN {}", cond.with(self.1), block.with(self.1)),
            Statement::Loop(block, _) => writeln!(f, "LOOP {}", block.with(self.1))
        }
    }
}

impl Display for WithProgram<'_, Value> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.0 {
            Value::Var(v, _) => write!(f, "{v:?}"),
            Value::Num(n, _) => write!(f, "{n}"),
            Value::Literal(l, _) => write!(f, "{:?}", self.1.literals[*l]),
            Value::Uninit(_) => write!(f, "---"),
            Value::Unit(_) => write!(f, "{{}}")
        }
    }
}

impl Display for WithProgram<'_, Expr<'_>> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.0 {
            Expr::Value(v) => write!(f, "{}", v.with(self.1)),
            Expr::Break(_) => write!(f, "break"),
            Expr::Continue(_) => write!(f, "continue"),
            Expr::Return(e, _) => match e {
                Some(e) => write!(f, "return with {}", e.with(self.1)),
                None => write!(f, "return")
            }
            Expr::FieldAccess(var, field, _) => write!(f, "{}.{field}", var.with(self.1)),
            Expr::PathAccess(ty, field, _) => write!(f, "get constant {field} from {ty:?}"),
            Expr::FuncCall(func, args, _) => {
                write!(f, "call {func:?} with (")?;
                for arg in args {
                    write!(f, "{}, ", arg.with(self.1))?;
                }
                write!(f, ")")
            }
            Expr::UnaryOp(op, var, _) => write!(f, "{op} {}", var.with(self.1)),
            Expr::BinOp(a, op, b, _) => write!(f, "{} {op} {}", a.with(self.1), b.with(self.1))
        }
    }
}

impl Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOp as O;
        let s = match self {
            O::Deref => "*",
            O::Negate => "-",
            O::AddressOf => "&",
            O::Not => "!"
        };
        write!(f, "{s}")
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp as O;
        let s = match self {
            O::Add => "+", O::Sub => "-", O::Mul => "*", O::Div => "/", O::Mod => "%",
            O::LogicAnd => "&&", O::LogicOr => "||", O::LogicXor => "^^",
            O::And => "&", O::Or => "|", O::Xor => "^",
            O::Eq => "==", O::Ne => "!=", O::Gt => ">", O::Ge => ">=", O::Lt => "<", O::Le => "<="
        };
        write!(f, "{s}")
    }
}
