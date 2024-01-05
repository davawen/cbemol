use crate::ast::Span;
use chumsky::{span::SimpleSpan, prelude::Rich};
use std::{fmt::{Display, Debug}, ops::Range};

use ariadne::{Report, ReportKind, Label, Color};

pub struct Error {
    pub message: String,
    pub label: Option<(Span, String)>
}

impl Error {
    pub fn new(message: impl ToString) -> Self {
        Self {
            message: message.to_string(),
            label: None
        }
    }

    pub fn with_label(mut self, span: Span, message: impl ToString) -> Self {
        self.label = Some((span, message.to_string()));
        self
    }

    pub fn err<T>(self) -> Result<T, Self> {
        Err(self)
    }

    pub fn errs<T>(self) -> Result<T, Vec<Self>> {
        Err(vec![self])
    }
}

pub trait CompilerError: Sized {
    fn map(self) -> impl CompilerError { self }
    fn span(&self) -> SimpleSpan;
    fn message(&self) -> String;
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>>;
}

impl<T: Clone + Display + Debug> CompilerError for Rich<'_, T> {
    fn map(self) -> impl CompilerError { self.map_token(|c| c.to_string()) }
    fn span(&self) -> SimpleSpan { *self.span() }
    fn message(&self) -> String { self.to_string() }
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>> {
        vec![
            Label::new((filename, self.span().into_range()))
                .with_message(format!("Expected: {:?}", self.expected().collect::<Vec<_>>()))
                .with_color(Color::Red)
        ]
    }
}

impl CompilerError for Error {
    fn span(&self) -> SimpleSpan {
        self.label.as_ref().map(|x| x.0).unwrap_or(SimpleSpan::new(0, 0))
    }
    fn message(&self) -> String { self.message.clone() }
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>> {
        self.label.into_iter().map(|(span, message)| 
            Label::new((filename, span.into_range()))
                .with_message(message)
                .with_color(Color::Red)
        ).collect()
    }
}

pub fn show_errs(src: &str, filename: &str, errs: Vec<impl CompilerError>) {
    let mut cache = (filename, src.into());

    errs.into_iter()
        .map(|e| e.map())
        .for_each(|e| {
            Report::build(ReportKind::Error, filename, e.span().start)
                .with_message(e.message())
                .with_labels(e.labels(filename))
                .finish()
                .eprint(&mut cache)
                .unwrap()
        });
}
