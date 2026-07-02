use crate::surface::ast::{
    BinaryOp, Binding, Boundedness, CaseArm, ConstructorDecl, Decl, EffectDecl, Expr, ExprKind,
    FieldDecl, FnDecl, HandleClause, Name, Param, Pattern, PrefixOp, Program, Span, Spanned,
    TypeDecl, TypeDeclKind, TypeExpr,
};
use crate::surface::lexer::{lex, LexError, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub span: Span,
    pub message: String,
}

impl From<LexError> for ParseError {
    fn from(value: LexError) -> Self {
        Self {
            span: value.span,
            message: value.message,
        }
    }
}

/// Parses the Sprint 05 subset of `docs/syntax.md Appendix A`.
pub fn parse_program(src: &str) -> Result<Program, ParseError> {
    let tokens = lex(src)?;
    Parser { tokens, idx: 0 }.program()
}

struct Parser {
    tokens: Vec<Token>,
    idx: usize,
}

impl Parser {
    fn program(&mut self) -> Result<Program, ParseError> {
        let mut decls = Vec::new();
        while !self.at(&TokenKind::Eof) {
            decls.push(self.decl()?);
        }
        Ok(Program { decls })
    }

    fn decl(&mut self) -> Result<Decl, ParseError> {
        let public = self.eat(&TokenKind::Pub).is_some();
        if self.at(&TokenKind::Fn) {
            return self.fn_decl(public).map(Decl::Fn);
        }
        if public {
            return Err(self.error_here("`pub` may only prefix `fn` in the reduced surface"));
        }
        if self.at(&TokenKind::Effect) {
            return self.effect_decl().map(Decl::Effect);
        }
        if self.at(&TokenKind::Type) {
            return self.type_decl().map(Decl::Type);
        }
        self.reject_unsupported_decl()?;
        Err(self.error_here("expected declaration"))
    }

    fn fn_decl(&mut self, public: bool) -> Result<FnDecl, ParseError> {
        // Function declarations: `docs/syntax.md §4` and Appendix A `fn_decl`.
        let start = self.expect(&TokenKind::Fn, "expected `fn`")?.span;
        let name = self.expect_ident("expected function name")?;
        if self.eat(&TokenKind::LBracket).is_some() {
            return Err(self.error_previous("type parameters are not yet in the reduced surface"));
        }
        self.expect(&TokenKind::LParen, "expected `(` after function name")?;
        let params = self.params()?;
        self.expect(&TokenKind::RParen, "expected `)` after parameters")?;
        self.expect(&TokenKind::Arrow, "expected `->` before return type")?;
        let ret = self.ty()?;
        let effects = if self.eat(&TokenKind::Bang).is_some() {
            let bang = self.previous().span;
            self.effect_row()?;
            Some(bang)
        } else {
            None
        };
        let boundedness = if self.eat(&TokenKind::Measure).is_some() {
            Boundedness::Measure(self.expr()?)
        } else if let Some(tok) = self.eat(&TokenKind::Div) {
            Boundedness::Div(tok.span)
        } else {
            Boundedness::Structural
        };
        let body = if self.eat(&TokenKind::Eq).is_some() {
            self.expr()?
        } else if self.at(&TokenKind::LBrace) {
            self.block()?
        } else {
            return Err(self.error_here("expected `=` expression or block body"));
        };
        let span = start.join(body.span);
        Ok(FnDecl {
            public,
            name,
            params,
            ret,
            effects,
            boundedness,
            body,
            span,
        })
    }

    fn type_decl(&mut self) -> Result<TypeDecl, ParseError> {
        // Nominal monomorphic aggregate declarations, `docs/syntax.md §3` and calculus §3.
        let start = self.expect(&TokenKind::Type, "expected `type`")?.span;
        let name = self.expect_ident("expected type name")?;
        if self.eat(&TokenKind::LBracket).is_some() {
            return Err(self.error_previous("type parameters are not yet in the reduced surface"));
        }
        self.expect(&TokenKind::Eq, "expected `=` in type declaration")?;
        let kind = if self.eat(&TokenKind::LBrace).is_some() {
            let mut fields = Vec::new();
            if !self.at(&TokenKind::RBrace) {
                loop {
                    let field = self.expect_ident("expected field name")?;
                    self.expect(&TokenKind::Colon, "expected `:` in record field")?;
                    let ty = self.ty()?;
                    fields.push(FieldDecl { name: field, ty });
                    if self.eat(&TokenKind::Comma).is_none() {
                        break;
                    }
                }
            }
            self.expect(&TokenKind::RBrace, "expected `}` after record type")?;
            TypeDeclKind::Record(fields)
        } else {
            let mut ctors = Vec::new();
            loop {
                let ctor = self.expect_ident("expected constructor name")?;
                let mut payloads = Vec::new();
                if self.eat(&TokenKind::LParen).is_some() {
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            payloads.push(self.ty()?);
                            if self.eat(&TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                    }
                    self.expect(
                        &TokenKind::RParen,
                        "expected `)` after constructor payloads",
                    )?;
                }
                ctors.push(ConstructorDecl {
                    name: ctor,
                    payloads,
                });
                if self.eat(&TokenKind::Pipe).is_none() {
                    break;
                }
            }
            TypeDeclKind::Variant(ctors)
        };
        let span = start.join(self.previous().span);
        Ok(TypeDecl { name, kind, span })
    }

    fn effect_decl(&mut self) -> Result<EffectDecl, ParseError> {
        // Reduced effect declaration, `docs/syntax.md §6` / Appendix A `effect_decl`.
        let start = self.expect(&TokenKind::Effect, "expected `effect`")?.span;
        let name = self.expect_ident("expected effect name")?;
        if self.eat(&TokenKind::LBracket).is_some() {
            return Err(
                self.error_previous("effect type parameters are not yet in the reduced surface")
            );
        }
        self.expect(&TokenKind::LBrace, "expected `{` in effect declaration")?;
        let op = self.expect_ident("expected operation name")?;
        self.expect(&TokenKind::LParen, "expected `(` in operation signature")?;
        let mut params = self.params()?;
        if params.len() != 1 {
            return Err(
                self.error_here("reduced core operation must have exactly one Nat parameter")
            );
        }
        let param = params.remove(0);
        self.expect(&TokenKind::RParen, "expected `)` in operation signature")?;
        self.expect(&TokenKind::Arrow, "expected `->` in operation signature")?;
        let ret = self.ty()?;
        let end = self
            .expect(&TokenKind::RBrace, "expected `}` after effect declaration")?
            .span;
        Ok(EffectDecl {
            name,
            op,
            param,
            ret,
            span: start.join(end),
        })
    }

    fn params(&mut self) -> Result<Vec<Param>, ParseError> {
        let mut params = Vec::new();
        if self.at(&TokenKind::RParen) {
            return Ok(params);
        }
        loop {
            let name = self.expect_ident("expected parameter name")?;
            self.expect(&TokenKind::Colon, "expected `:` after parameter name")?;
            let ty = self.ty()?;
            params.push(Param { name, ty });
            if self.eat(&TokenKind::Comma).is_none() {
                break;
            }
        }
        Ok(params)
    }

    fn ty(&mut self) -> Result<TypeExpr, ParseError> {
        if let Some(caret) = self.eat(&TokenKind::Caret) {
            let inner = self.ty_atom()?;
            let span = caret.span.join(inner.span());
            let unique = TypeExpr::Unique(Box::new(inner), span);
            if self.eat(&TokenKind::Arrow).is_some() {
                let right = self.ty()?;
                let span = unique.span().join(right.span());
                return Ok(TypeExpr::Arrow(Box::new(unique), Box::new(right), span));
            }
            return Ok(unique);
        }
        let left = self.ty_atom()?;
        if self.eat(&TokenKind::Arrow).is_some() {
            let right = self.ty()?;
            let span = left.span().join(right.span());
            Ok(TypeExpr::Arrow(Box::new(left), Box::new(right), span))
        } else {
            Ok(left)
        }
    }

    fn ty_atom(&mut self) -> Result<TypeExpr, ParseError> {
        let tok = self.advance().clone();
        match tok.kind {
            TokenKind::Ident(name) if name == "Unit" => Ok(TypeExpr::Unit(tok.span)),
            TokenKind::Ident(name) if name == "Nat" => Ok(TypeExpr::Nat(tok.span)),
            TokenKind::Ident(name) if name == "Array" => Ok(TypeExpr::Array(tok.span)),
            TokenKind::Ident(name) => Ok(TypeExpr::Named(name, tok.span)),
            TokenKind::LParen => {
                if self.eat(&TokenKind::RParen).is_some() {
                    Ok(TypeExpr::Unit(tok.span.join(self.previous().span)))
                } else {
                    let inner = self.ty()?;
                    self.expect(&TokenKind::RParen, "expected `)` after type")?;
                    Ok(inner)
                }
            }
            _ => Err(ParseError {
                span: tok.span,
                message: "expected type".into(),
            }),
        }
    }

    fn effect_row(&mut self) -> Result<(), ParseError> {
        if self.eat(&TokenKind::LBrace).is_some() {
            // Surface multi-label rows (`docs/syntax.md §3`, §6) parse as finite label lists;
            // the reduced elaborator/checker carry the actual set in core effects.
            self.expect_ident("expected effect label")?;
            while self.eat(&TokenKind::Comma).is_some() {
                self.expect_ident("expected effect label after `,`")?;
            }
            self.expect(&TokenKind::RBrace, "expected `}` after effect row")?;
            Ok(())
        } else {
            let grade = self.expect_ident("expected effect row after `!`")?;
            Err(ParseError {
                span: grade.span,
                message: "effect-row variables are not yet in the reduced surface".into(),
            })
        }
    }

    fn expr(&mut self) -> Result<Expr, ParseError> {
        self.pipe_expr()
    }

    fn pipe_expr(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.add_expr()?;
        while self.eat(&TokenKind::PipeGt).is_some() {
            // Pipe into prefix forms, `docs/syntax.md §5`: `x |> freeze` / `x |> move`
            // are operand-less RHS shorthands for `freeze x` / `move x`.
            if let Some(op) = self.operandless_pipe_prefix() {
                let tok = self.advance().clone();
                let span = lhs.span.join(tok.span);
                lhs = Expr::new(
                    ExprKind::Prefix {
                        op,
                        expr: Box::new(lhs),
                    },
                    span,
                );
                continue;
            }
            let rhs = self.add_expr()?;
            let span = lhs.span.join(rhs.span);
            lhs = Expr::new(
                ExprKind::Pipe {
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn operandless_pipe_prefix(&self) -> Option<PrefixOp> {
        let op = match self.peek().kind {
            TokenKind::Move => PrefixOp::Move,
            TokenKind::Freeze => PrefixOp::Freeze,
            TokenKind::Inplace => return None,
            _ => return None,
        };
        let Some(next) = self.tokens.get(self.idx + 1) else {
            return Some(op);
        };
        if matches!(
            next.kind,
            TokenKind::PipeGt | TokenKind::RBrace | TokenKind::Semi | TokenKind::Eof
        ) {
            Some(op)
        } else {
            None
        }
    }

    fn add_expr(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.mul_expr()?;
        loop {
            let op = if self.eat(&TokenKind::Plus).is_some() {
                Some(BinaryOp::Add)
            } else if self.eat(&TokenKind::Minus).is_some() {
                Some(BinaryOp::Sub)
            } else {
                None
            };
            let Some(op) = op else {
                return Ok(lhs);
            };
            let rhs = self.mul_expr()?;
            let span = lhs.span.join(rhs.span);
            lhs = Expr::new(
                ExprKind::Binary {
                    op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
    }

    fn mul_expr(&mut self) -> Result<Expr, ParseError> {
        let mut lhs = self.call_expr()?;
        while self.eat(&TokenKind::Star).is_some() {
            let rhs = self.call_expr()?;
            let span = lhs.span.join(rhs.span);
            lhs = Expr::new(
                ExprKind::Binary {
                    op: BinaryOp::Mul,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
                span,
            );
        }
        Ok(lhs)
    }

    fn call_expr(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.primary()?;
        loop {
            if self.eat(&TokenKind::Dot).is_some() {
                let field = self.expect_ident("expected field or operation name after `.`")?;
                if self.eat(&TokenKind::LParen).is_some() {
                    let args = self.args()?;
                    let rparen = self.expect(&TokenKind::RParen, "expected `)` after arguments")?;
                    let effect = match expr.kind {
                        ExprKind::Var(name) => name,
                        _ => {
                            return Err(ParseError {
                                span: expr.span,
                                message: "effect calls must be written as `Effect.op(...)`".into(),
                            })
                        }
                    };
                    let span = expr.span.join(rparen.span);
                    expr = Expr::new(
                        ExprKind::QualifiedCall {
                            effect,
                            op: field.node,
                            args,
                        },
                        span,
                    );
                } else {
                    let span = expr.span.join(field.span);
                    expr = Expr::new(
                        ExprKind::Field {
                            record: Box::new(expr),
                            field,
                        },
                        span,
                    );
                }
            } else if self.eat(&TokenKind::LParen).is_some() {
                let args = self.args()?;
                let rparen = self.expect(&TokenKind::RParen, "expected `)` after arguments")?;
                let span = expr.span.join(rparen.span);
                expr = Expr::new(
                    ExprKind::Call {
                        callee: Box::new(expr),
                        args,
                    },
                    span,
                );
            } else {
                return Ok(expr);
            }
        }
    }

    fn args(&mut self) -> Result<Vec<Expr>, ParseError> {
        let mut args = Vec::new();
        if self.at(&TokenKind::RParen) {
            return Ok(args);
        }
        loop {
            args.push(self.expr()?);
            if self.eat(&TokenKind::Comma).is_none() {
                break;
            }
        }
        Ok(args)
    }

    fn primary(&mut self) -> Result<Expr, ParseError> {
        self.reject_unsupported_expr()?;
        let tok = self.advance().clone();
        match tok.kind {
            TokenKind::Move | TokenKind::Inplace | TokenKind::Freeze => {
                let op = match tok.kind {
                    TokenKind::Move => PrefixOp::Move,
                    TokenKind::Inplace => PrefixOp::Inplace,
                    TokenKind::Freeze => PrefixOp::Freeze,
                    _ => unreachable!("matched prefix token"),
                };
                let expr = self.call_expr()?;
                Ok(Expr::new(
                    ExprKind::Prefix {
                        op,
                        expr: Box::new(expr.clone()),
                    },
                    tok.span.join(expr.span),
                ))
            }
            TokenKind::Number(value) => Ok(Expr::new(ExprKind::Nat(value), tok.span)),
            TokenKind::Ident(name) => Ok(Expr::new(ExprKind::Var(name), tok.span)),
            TokenKind::Underscore => Ok(Expr::new(ExprKind::Var("_".into()), tok.span)),
            TokenKind::LParen => {
                if self.eat(&TokenKind::RParen).is_some() {
                    Ok(Expr::new(
                        ExprKind::Unit,
                        tok.span.join(self.previous().span),
                    ))
                } else {
                    let inner = self.expr()?;
                    let end = self
                        .expect(&TokenKind::RParen, "expected `)` after expression")?
                        .span;
                    Ok(Expr::new(inner.kind, tok.span.join(end)))
                }
            }
            TokenKind::LBrace => self.block_after_lbrace(tok.span),
            TokenKind::Dot => self.record_after_dot(tok.span),
            TokenKind::Case => self.case_after_keyword(tok.span),
            TokenKind::Handle => self.handle_after_keyword(tok.span),
            _ => Err(ParseError {
                span: tok.span,
                message: "expected expression".into(),
            }),
        }
    }

    fn record_after_dot(&mut self, dot: Span) -> Result<Expr, ParseError> {
        // Record literal/update surface, `docs/syntax.md §3/§5`.
        self.expect(&TokenKind::LBrace, "expected `{` after `.`")?;
        if self.looks_like_record_update() {
            let record = self.expr()?;
            self.expect(&TokenKind::Pipe, "expected `|` in record update")?;
            let field = self.expect_ident("expected field name in record update")?;
            self.expect(&TokenKind::Eq, "expected `=` in record update")?;
            let value = self.expr()?;
            let end = self
                .expect(&TokenKind::RBrace, "expected `}` after record update")?
                .span;
            return Ok(Expr::new(
                ExprKind::RecordUpdate {
                    record: Box::new(record),
                    field,
                    value: Box::new(value),
                },
                dot.join(end),
            ));
        }
        let mut fields = Vec::new();
        if !self.at(&TokenKind::RBrace) {
            loop {
                let name = self.expect_ident("expected record field")?;
                self.expect(&TokenKind::Eq, "expected `=` in record literal field")?;
                let expr = self.expr()?;
                fields.push((name, expr));
                if self.eat(&TokenKind::Comma).is_none() {
                    break;
                }
            }
        }
        let end = self
            .expect(&TokenKind::RBrace, "expected `}` after record literal")?
            .span;
        Ok(Expr::new(ExprKind::RecordLit(fields), dot.join(end)))
    }

    fn looks_like_record_update(&self) -> bool {
        let mut depth = 0usize;
        let mut idx = self.idx;
        while let Some(tok) = self.tokens.get(idx) {
            match tok.kind {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                TokenKind::Pipe if depth == 0 => return true,
                TokenKind::Eof => return false,
                _ => {}
            }
            idx += 1;
        }
        false
    }

    fn block(&mut self) -> Result<Expr, ParseError> {
        let start = self.expect(&TokenKind::LBrace, "expected `{`")?.span;
        self.block_after_lbrace(start)
    }

    fn block_after_lbrace(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Blocks as expressions, `docs/syntax.md §2`.
        let mut bindings = Vec::new();
        while !self.at(&TokenKind::RBrace) && self.is_ident_eq() {
            let name = self.expect_ident("expected binding name")?;
            self.expect(&TokenKind::Eq, "expected `=` in block binding")?;
            let expr = self.expr()?;
            let span = name.span.join(expr.span);
            bindings.push(Binding { name, expr, span });
            self.eat(&TokenKind::Semi);
        }
        let result = if self.at(&TokenKind::RBrace) {
            Expr::new(ExprKind::Unit, self.peek().span)
        } else {
            let expr = self.expr()?;
            self.eat(&TokenKind::Semi);
            expr
        };
        let end = self
            .expect(&TokenKind::RBrace, "expected `}` after block")?
            .span;
        Ok(Expr::new(
            ExprKind::Block {
                bindings,
                result: Box::new(result),
            },
            start.join(end),
        ))
    }

    fn case_after_keyword(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Reduced Nat eliminator surface, `docs/syntax.md §5`.
        let scrutinee = self.expr()?;
        self.expect(&TokenKind::LBrace, "expected `{` after case scrutinee")?;
        let mut arms = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            let pattern = self.pattern()?;
            self.expect(&TokenKind::Arrow, "expected `->` in case arm")?;
            let body = self.expr()?;
            let span = pattern.span().join(body.span);
            arms.push(CaseArm {
                pattern,
                body,
                span,
            });
            self.eat(&TokenKind::Semi);
        }
        let end = self
            .expect(&TokenKind::RBrace, "expected `}` after case")?
            .span;
        Ok(Expr::new(
            ExprKind::CaseNat {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            start.join(end),
        ))
    }

    fn handle_after_keyword(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Handlers, `docs/syntax.md §6`.
        let body = self.expr()?;
        self.expect(&TokenKind::LBrace, "expected `{` after handled expression")?;
        let mut clauses = Vec::new();
        while !self.at(&TokenKind::RBrace) {
            clauses.push(self.handle_clause()?);
            self.eat(&TokenKind::Semi);
        }
        let end = self
            .expect(&TokenKind::RBrace, "expected `}` after handler")?
            .span;
        Ok(Expr::new(
            ExprKind::Handle {
                body: Box::new(body),
                clauses,
            },
            start.join(end),
        ))
    }

    fn handle_clause(&mut self) -> Result<HandleClause, ParseError> {
        if let Some(return_tok) = self.eat(&TokenKind::Return) {
            self.expect(&TokenKind::LParen, "expected `(` after return")?;
            let var = self.expect_ident("expected return binder")?;
            self.expect(&TokenKind::RParen, "expected `)` after return binder")?;
            self.expect(&TokenKind::Arrow, "expected `->` in return clause")?;
            let body = self.expr()?;
            return Ok(HandleClause::Return {
                var,
                span: return_tok.span.join(body.span),
                body,
            });
        }
        let effect = self.expect_ident("expected effect label in handler clause")?;
        self.expect(&TokenKind::Dot, "expected `.` in operation clause")?;
        let op = self.expect_ident("expected operation name")?;
        self.expect(&TokenKind::LParen, "expected `(` after operation name")?;
        let param = self.pattern()?;
        self.expect(&TokenKind::RParen, "expected `)` after operation pattern")?;
        self.expect(&TokenKind::Comma, "expected `,` before continuation binder")?;
        let kont = self.pattern()?;
        self.expect(&TokenKind::Arrow, "expected `->` in operation clause")?;
        let body = self.expr()?;
        Ok(HandleClause::Operation {
            span: effect.span.join(body.span),
            effect,
            op,
            param,
            kont,
            body,
        })
    }

    fn pattern(&mut self) -> Result<Pattern, ParseError> {
        let tok = self.advance().clone();
        match tok.kind {
            TokenKind::Number(0) => Ok(Pattern::Zero(tok.span)),
            TokenKind::Number(_) => Err(ParseError {
                span: tok.span,
                message: "only `0` literal patterns are in the reduced surface".into(),
            }),
            TokenKind::Ident(name) => {
                let spanned = Spanned::new(name, tok.span);
                if self.eat(&TokenKind::LParen).is_some() {
                    let mut args = Vec::new();
                    if !self.at(&TokenKind::RParen) {
                        loop {
                            args.push(self.pattern()?);
                            if self.eat(&TokenKind::Comma).is_none() {
                                break;
                            }
                        }
                    }
                    let end = self
                        .expect(&TokenKind::RParen, "expected `)` after constructor pattern")?
                        .span;
                    Ok(Pattern::Constructor {
                        name: spanned,
                        args,
                        span: tok.span.join(end),
                    })
                } else if spanned.node.chars().next().is_some_and(char::is_uppercase) {
                    Ok(Pattern::Constructor {
                        name: spanned,
                        args: Vec::new(),
                        span: tok.span,
                    })
                } else {
                    Ok(Pattern::Bind(spanned))
                }
            }
            TokenKind::Dot => {
                self.expect(
                    &TokenKind::LBrace,
                    "expected `{` after `.` in record pattern",
                )?;
                let mut fields = Vec::new();
                if !self.at(&TokenKind::RBrace) {
                    loop {
                        fields.push(self.expect_ident("expected field name in record pattern")?);
                        if self.eat(&TokenKind::Comma).is_none() {
                            break;
                        }
                    }
                }
                let end = self
                    .expect(&TokenKind::RBrace, "expected `}` after record pattern")?
                    .span;
                Ok(Pattern::Record {
                    fields,
                    span: tok.span.join(end),
                })
            }
            TokenKind::Underscore => Ok(Pattern::Wildcard(tok.span)),
            _ => Err(ParseError {
                span: tok.span,
                message: "expected pattern".into(),
            }),
        }
    }

    fn reject_unsupported_decl(&self) -> Result<(), ParseError> {
        let msg = match self.peek().kind {
            TokenKind::Type => Some("type declarations are not yet in the reduced surface"),
            TokenKind::Use => Some("modules/use are not yet in the reduced surface"),
            _ => None,
        };
        if let Some(message) = msg {
            Err(ParseError {
                span: self.peek().span,
                message: message.into(),
            })
        } else {
            Ok(())
        }
    }

    fn reject_unsupported_expr(&self) -> Result<(), ParseError> {
        let msg = match self.peek().kind {
            TokenKind::If => Some("if is not yet in the reduced surface; use `case` on Nat"),
            TokenKind::Spawn => Some("spawn is not yet in the reduced surface"),
            TokenKind::Scope => Some("scope is not yet in the reduced surface"),
            TokenKind::LBracket => Some("lists are not yet in the reduced surface"),
            _ => None,
        };
        if let Some(message) = msg {
            Err(ParseError {
                span: self.peek().span,
                message: message.into(),
            })
        } else {
            Ok(())
        }
    }

    fn is_ident_eq(&self) -> bool {
        matches!(self.peek().kind, TokenKind::Ident(_))
            && matches!(
                self.tokens.get(self.idx + 1).map(|t| &t.kind),
                Some(TokenKind::Eq)
            )
    }

    fn expect_ident(&mut self, message: &str) -> Result<Spanned<Name>, ParseError> {
        let tok = self.advance().clone();
        match tok.kind {
            TokenKind::Ident(name) => Ok(Spanned::new(name, tok.span)),
            _ => Err(ParseError {
                span: tok.span,
                message: message.into(),
            }),
        }
    }

    fn expect(&mut self, kind: &TokenKind, message: &str) -> Result<Token, ParseError> {
        if self.at(kind) {
            Ok(self.advance().clone())
        } else {
            Err(self.error_here(message))
        }
    }

    fn eat(&mut self, kind: &TokenKind) -> Option<Token> {
        if self.at(kind) {
            Some(self.advance().clone())
        } else {
            None
        }
    }

    fn at(&self, kind: &TokenKind) -> bool {
        std::mem::discriminant(&self.peek().kind) == std::mem::discriminant(kind)
    }

    fn peek(&self) -> &Token {
        &self.tokens[self.idx]
    }

    fn previous(&self) -> &Token {
        &self.tokens[self.idx - 1]
    }

    fn advance(&mut self) -> &Token {
        let idx = self.idx;
        if self.idx + 1 < self.tokens.len() {
            self.idx += 1;
        }
        &self.tokens[idx]
    }

    fn error_here(&self, message: &str) -> ParseError {
        ParseError {
            span: self.peek().span,
            message: message.into(),
        }
    }

    fn error_previous(&self, message: &str) -> ParseError {
        ParseError {
            span: self.previous().span,
            message: message.into(),
        }
    }
}
