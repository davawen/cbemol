use super::*;

impl std::fmt::Display for Ast<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const GRAY: &str = "\x1b[90m";
        const RESET: &str = "\x1b[0m";
        const ORANGE: &str = "\x1b[33m";
        const GREEN: &str = "\x1b[32m";
        const MAGENTA: &str = "\x1b[34m";
        const CYAN: &str = "\x1b[36m";

        use Ast as A;
        match self {
            A::Id(id, span)                 => write!(f, "{GRAY}{span} {MAGENTA}IDENT {RESET}{id}"),
            A::Num(n, span)                 => write!(f, "{GRAY}{span} {MAGENTA}NUM {ORANGE}{n}{RESET}"),
            A::Literal(l, span)             => write!(f, "{GRAY}{span} {MAGENTA}LITERAL {GREEN}{l:?}{RESET}"),
            A::Shorthand(span)              => write!(f, "{GRAY}{span} {MAGENTA}SHORTHAND {RESET}"),
            A::Uninit(span)                 => write!(f, "{GRAY}{span} {MAGENTA}UNINIT {RESET}"),
            A::UnaryExpr(op, e, span)       => write!(f, "{GRAY}{span} {MAGENTA}OP {RESET}{op} {e}"),
            A::BinExpr(a, op, b, span)      => write!(f, "{GRAY}{span} {MAGENTA}OP {RESET}{op} {a} {b}"),
            A::Access(e, name, span)        => write!(f, "{GRAY}{span} {RESET}{e}.{name}"),
            A::Assign { var, value, span }  => write!(f, "{GRAY}{span} {MAGENTA}ASSIGN {RESET}{var} = {value}"),
            A::IfExpr { cond, block, span } => write!(f, "{GRAY}{span} {MAGENTA}IF {RESET}{cond} THEN {block}"),
            A::LoopExpr(block, span)        => write!(f, "{GRAY}{span} {MAGENTA}LOOP {RESET}{block}"),
            A::Break(Some(e), span)         => write!(f, "{GRAY}{span} {MAGENTA}BREAK {RESET}{e}"),
            A::Break(None, span)            => write!(f, "{GRAY}{span} {MAGENTA}BREAK {RESET}"),
            A::Continue(Some(e), span)      => write!(f, "{GRAY}{span} {MAGENTA}CONTINUE{RESET} {e}"),
            A::Continue(None, span)         => write!(f, "{GRAY}{span} {MAGENTA}CONTINUE{RESET}"),
            A::Block(b, span)               => write!(f, "{GRAY}{span} {RESET}{b}"),
            A::ForExpr { decl: (ty, name), it, body, span } => 
                write!(f, "{GRAY}{span} {MAGENTA}FOR {CYAN}{ty} {RESET}{name} IN {it} {body}"),
            A::Declare { var, ty, value: Some(value), span } => 
                write!(f, "{GRAY}{span} {MAGENTA}DECLARE {CYAN}{ty} {RESET}{var} = {value}"),
            A::Declare { var, ty, value: None, span } => 
                write!(f, "{GRAY}{span} {MAGENTA}DECLARE {CYAN}{ty} {RESET}{var}"),
            A::FuncCall { name, args, span } => {
                write!(f, "{GRAY}{span} {MAGENTA}CALL {RESET}{name} (")?;
                for arg in args {
                    if let (Some(arg), expr, _) = arg {
                        write!(f, "{arg} = {expr}, ")?;
                    } else {
                        write!(f, "{}", arg.1)?;
                    }
                }
                write!(f, ")")
            }
            A::FunctionDef { name, ret, params, body, span } => {
                write!(f, "{GRAY}{span} {MAGENTA}DEFINE FUNC {CYAN}{ret} {RESET}{name} (")?;
                for param in params {
                    write!(f, "{param}")?;
                }
                write!(f, ") {body}")
            }
            A::StructDef { name, fields, span } => {
                writeln!(f, "{GRAY}{span} {MAGENTA}DEFINE STRUCT {CYAN}{name}{RESET} {{")?;
                for (ty, name) in fields {
                    writeln!(f, "  {CYAN}{ty} {RESET}{name};")?;
                }
                write!(f, "}}")
            }
            A::EnumDef { name, variants, span } => {
                writeln!(f, "{GRAY}{span} {MAGENTA}DEFINE ENUM {CYAN}{name} {RESET}{{")?;
                for (name, value) in variants {
                    write!(f, "  {name}")?;
                    if let Some(value) = value {
                        write!(f, " = {ORANGE}{value}{RESET}")?;
                    }
                    writeln!(f, ";")?;
                }
                write!(f, "}}")
            }
            A::UnionDef { name, variants, span } => {
                writeln!(f, "{GRAY}{span} {MAGENTA}DEFINE UNION {CYAN}{name} {RESET}{{")?;
                for (ty, name) in variants {
                    writeln!(f, "  {CYAN}{ty} {RESET}{name};")?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl std::fmt::Display for Parameter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        const CYAN: &str = "\x1b[36m";
        const RESET: &str = "\x1b[0m";
        if let Some(name) = self.outward_name {
            write!(f, "{name}: ")?;
        }
        write!(f, "{CYAN}{} {RESET}{}", self.ty, self.name)?;
        if let Some(value) = &self.value {
            write!(f, " = {value}")?;
        }
        Ok(())
    }
}

impl std::fmt::Display for Block<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use std::fmt::Write;
        let mut s = String::new();
        for statement in &self.0 {
            writeln!(s, "{statement};")?;
        }

        if let Some(expr) = &self.1 {
            writeln!(s, "{expr}")?;
        }

        writeln!(f, "{{")?;
        for line in s.lines() {
            writeln!(f, "  {line}")?;
        }
        write!(f, "}}")
    }
}

impl std::fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type as T;
        match self {
            T::Id(id, _) => write!(f, "{id}"),
            T::Pointer(ty, _) => write!(f, "{ty}&"),
            T::FunctionPointer { ret, args, span: _ } => {
                write!(f, "{ret}(")?;
                for arg in args {
                    write!(f, "{arg}, ")?;
                }
                write!(f, ")")
            }
            T::Array { ty, len, span: _ } => write!(f, "{ty}[{len}]"),
            T::Slice(ty, _) => write!(f, "{ty}[]")
        }
    }
}

impl std::fmt::Display for LValue<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use LValue as L;
        match self {
            L::Id(id) => write!(f, "{id}"),
            L::Deref(l) => write!(f, "*{l}"),
            L::Index(l, i) => write!(f, "{l}[{i}]")
        }
    }
}

impl std::fmt::Display for UnaryOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use UnaryOp as O;
        let s = match self {
            O::Not => "!", O::Deref => "*",
            O::Negate => "-", O::AddressOf => "&"
        };
        write!(f, "{s}")
    }
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BinOp as O;
        let s = match self {
            O::Add => "+", O::Sub => "-", O::Mul => "*", O::Div => "/", O::Mod => "%",
            O::BinAnd => "&&", O::BinOr => "||", O::BinXor => "^^",
            O::And => "&", O::Or => "|", O::Xor => "^",
            O::Eq => "==", O::Ne => "!=", O::Gt => ">", O::Ge => ">=", O::Lt => "<", O::Le => "<=",
            O::Range => "..",
            O::Pipe => "|>"
        };
        write!(f, "{s}")
    }
}
