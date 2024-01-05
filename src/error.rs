use crate::ast::Span;
use chumsky::{span::{SimpleSpan, Span as SpanTrait}, prelude::Rich};
use std::{fmt::{Display, Debug}, ops::Range};

use ariadne::{Report, ReportKind, Label, Color, ColorGenerator};

pub struct Error {
    message: String,
    labels: Vec<(Span, String, usize)>,
    color_idx: usize
}

impl Error {
    pub fn new(message: impl ToString) -> Self {
        Self {
            message: message.to_string(),
            labels: Vec::new(),
            color_idx: 0
        }
    }

    /// get a new color for the next label
    pub fn col(mut self) -> Self {
        self.color_idx += 1;
        self
    }

    /// add a label to the error
    pub fn with_label(mut self, span: Span, message: impl ToString) -> Self {
        self.labels.push((span, message.to_string(), self.color_idx));
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
        self.labels.iter().map(|(span, _, _)| *span).reduce(|acc, x| acc.union(x))
            .unwrap_or(SimpleSpan::splat(0))
    }

    fn message(&self) -> String { self.message.clone() }
    fn labels(self, filename: &str) -> Vec<Label<(&str, Range<usize>)>> {
        let mut gen = ColorGenerator::from_state([59400, 12309, 320], 0.5); // random state just to avoid the default ugly pink
        let mut colors = vec![ Color::Red ];
        colors.extend((0..self.color_idx).map(|_| gen.next()));

        self.labels.into_iter().map(|(span, message, idx)| 
            Label::new((filename, span.into_range()))
                .with_message(message)
                .with_color(colors[idx])
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
