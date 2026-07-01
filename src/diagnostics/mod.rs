//! Unified source diagnostics for lexer/parser/elaborator/checker errors.

use crate::check::{TypeError, TypeErrorKind};
use crate::elaborate::{ElaborateError, SpanTable};
use crate::surface::ast::Span;
use crate::surface::ParseError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExitCode {
    Ok = 0,
    Diagnostics = 1,
    Internal = 2,
}

pub trait SourceError {
    fn span(&self) -> Span;
    fn message(&self) -> String;
}

impl SourceError for ParseError {
    fn span(&self) -> Span {
        self.span
    }

    fn message(&self) -> String {
        self.message.clone()
    }
}

impl SourceError for ElaborateError {
    fn span(&self) -> Span {
        self.span
    }

    fn message(&self) -> String {
        self.message.clone()
    }
}

#[must_use]
pub fn render_source_error(path: &str, src: &str, err: &impl SourceError) -> String {
    render(path, src, err.span(), &err.message())
}

#[must_use]
pub fn render_type_error(path: &str, src: &str, err: &TypeError, spans: &SpanTable) -> String {
    let span = match &*err.kind {
        TypeErrorKind::HandlerContinuationUsage(message) => continuation_span(message, spans)
            .or_else(|| spans.span_for_term_string(&err.term))
            .unwrap_or_default(),
        _ => spans.span_for_term_string(&err.term).unwrap_or_default(),
    };
    render(path, src, span, &err.to_string())
}

fn continuation_span(message: &str, spans: &SpanTable) -> Option<Span> {
    let start = message.find('`')? + 1;
    let end = message[start..].find('`')? + start;
    spans.span_for_var(&message[start..end])
}

fn render(path: &str, src: &str, span: Span, message: &str) -> String {
    let (line_no, col_no, line_start, line_end) = line_info(src, span.start);
    let line = &src[line_start..line_end];
    let caret_start = span.start.saturating_sub(line_start).min(line.len());
    let caret_len = span
        .end
        .saturating_sub(span.start)
        .max(1)
        .min(line.len().saturating_sub(caret_start).max(1));
    format!(
        "error: {message}\n --> {path}:{line_no}:{col_no}\n  |\n{line_no:>2} | {line}\n  | {}{}\n",
        " ".repeat(caret_start),
        "^".repeat(caret_len)
    )
}

fn line_info(src: &str, offset: usize) -> (usize, usize, usize, usize) {
    let mut line_no = 1;
    let mut line_start = 0;
    for (idx, ch) in src.char_indices() {
        if idx >= offset {
            break;
        }
        if ch == '\n' {
            line_no += 1;
            line_start = idx + 1;
        }
    }
    let line_end = src[line_start..]
        .find('\n')
        .map_or(src.len(), |rel| line_start + rel);
    let col_no = offset.saturating_sub(line_start) + 1;
    (line_no, col_no, line_start, line_end)
}
