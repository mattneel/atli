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

    fn secondary_span(&self) -> Option<(Span, String)> {
        None
    }
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
        sanitize_consumption_message(&self.message)
    }

    fn secondary_span(&self) -> Option<(Span, String)> {
        consumed_span_from_message(&self.message)
            .map(|span| (span, "first consumption here".to_string()))
    }
}

#[must_use]
pub fn render_source_error(path: &str, src: &str, err: &impl SourceError) -> String {
    let mut rendered = render(path, src, err.span(), &err.message());
    if let Some((span, label)) = err.secondary_span() {
        rendered.push_str(&render_note(path, src, span, &label));
    }
    rendered
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

fn render_note(path: &str, src: &str, span: Span, message: &str) -> String {
    let (line_no, col_no, line_start, line_end) = line_info(src, span.start);
    let line = &src[line_start..line_end];
    let caret_start = span.start.saturating_sub(line_start).min(line.len());
    let caret_len = span
        .end
        .saturating_sub(span.start)
        .max(1)
        .min(line.len().saturating_sub(caret_start).max(1));
    format!(
        "note: {message}
 --> {path}:{line_no}:{col_no}
  |
{line_no:>2} | {line}
  | {}{}
",
        " ".repeat(caret_start),
        "^".repeat(caret_len)
    )
}

fn sanitize_consumption_message(message: &str) -> String {
    if let Some(before_bytes) = message.split(" -> bytes ").next() {
        if message.contains("consumed here -> bytes ")
            && message.contains("; used again here -> bytes ")
        {
            return before_bytes.replace("consumed here", "consumed here; used again here");
        }
    }
    message.to_string()
}

fn consumed_span_from_message(message: &str) -> Option<Span> {
    let marker = "consumed here -> bytes ";
    let start = message.find(marker)? + marker.len();
    let rest = &message[start..];
    let (lo, rest) = rest.split_once("..")?;
    let hi = rest.split(';').next()?;
    Some(Span {
        start: lo.parse().ok()?,
        end: hi.parse().ok()?,
    })
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
