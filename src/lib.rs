//! A macro for creating format-like macros
//!
//! Have you ever wanted to emulate the functionality of the `format!`
//! family of macros, but with an output that is not a [`String`] or
//! something built from a [`String`]?
//!
//! No?
//!
//! Well, still, this might still be interesting for you.
//!
//! `format-like` aims to let _you_ decide how to interpret what is
//! inside `{}` pairs, instead of calling something like
//! `std::fmt::Display::fmt(&value)`.
//!
//! Additionaly, it lets you create 3 other types of bracket pairs:
//! `()`, `[]` and `<>`, so you can interpret things in even more
//! ways! This does of course come with the regular escaping that the
//! [`format!`] macro does, so `{{` is escaped to just `{`, the same
//! being the case for the other delimiters as well.
//!
//! Here's how it works:
//!
//! ```rust
//! # #![feature(decl_macro)]
//! use format_like::format_like;
//!
//! struct CommentedString(String, Vec<(usize, String)>);
//!
//! let comment = "there is an error in this word";
//! let text = "text";
//! let range = 0..usize::MAX;
//!
//! let commented_string = format_like!(
//!     parse_str,
//!     [('{', parse_interpolation, false), ('<', parse_comment, true)],
//!     CommentedString(String::new(), Vec::new()),
//!     "This is <comment>regluar {}, interpolated and commented {range.end}",
//!     text
//! );
//! # macro parse_str($value:expr, $str:literal) {{ $value }}
//! # macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{ $value }}
//! # macro parse_comment($value:expr, $modif:literal, $added:expr) {{ $value }}
//! ```
//!
//! In this example, the `{}` should work as intended, but you also
//! have access to `<>` interpolation. Inside `<>`, a comment will be
//! added, with the associated `usize` being its position in the
//! [`String`].
//!
//! This will all be done through the `parse_str`,
//! `parse_interpolation` and `parse_comment` macros:
//!
//! ```rust
//! #![feature(decl_macro)]
//! macro parse_str($value:expr, $str:literal) {{
//!     let mut commented_string = $value;
//!     commented_string.0.push_str($str);
//!     commented_string
//! }}
//!
//! macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{
//!     let CommentedString(string, comments) = $value;
//!     let string = format!(concat!("{}{", $modif, "}"), string, $added);
//!     CommentedString(string, comments)
//! }}
//!
//! macro parse_comment($value:expr, $_modif:literal, $added:expr) {{
//!     let mut commented_string = $value;
//!     commented_string
//!         .1
//!         .push((commented_string.0.len(), $added.to_string()));
//!     commented_string
//! }}
//! ```
//!
//! The `parse_str` macro will be responsible for handling the non
//! `{}` or `<>` parts of the literal `&str`. The `parse_comment` and
//! `parse_interpolation` methods will handle what's inside the `<>`
//! and `{}` pairs, respectively.
//!
//! `parse_comment` and `parse_interpolation` must have three
//! parameters, one for the `value` being modified (in this case, a
//! `CommentedString`), one for the modifier (`"?", "#?", ".3", etc),
//! which might come after a `":"` in the pair. and one for the object
//! being added (it's [`Display`] objects in this case, but
//! it could be anything else).
//!
//! Now, as I mentioned earlier, this crate is meant for you to create
//! _your own_ format like macros, so you should package all of this
//! up into a single macro, like this:
//!
//! ```rust
//! #![feature(decl_macro)]
//! use format_like::format_like;
//!
//! #[derive(Debug, PartialEq)]
//! struct CommentedString(String, Vec<(usize, String)>);
//!
//! let comment = "there is an error in this word";
//! let text = "text";
//! let range = 0..usize::MAX;
//!
//! let commented_string = commented_string!(
//!     "This is <comment>regluar {}, interpolated and commented {range.end}",
//!     text
//! );
//!
//! assert_eq!(
//!     commented_string,
//!     CommentedString(
//!         "This is regluar text, interpolated and commented 18446744073709551615".to_string(),
//!         vec![(8, "there is an error in this word".to_string())]
//!     )
//! );
//!
//! macro commented_string($($parts:tt)*) {
//!     format_like!(
//!         parse_str,
//!         [('{', parse_interpolation, false), ('<', parse_comment, true)],
//!         CommentedString(String::new(), Vec::new()),
//!         $($parts)*
//!     )
//! }
//!
//! macro parse_str($value:expr, $str:literal) {{
//!     let mut commented_string = $value;
//!     commented_string.0.push_str($str);
//!     commented_string
//! }}
//!
//! macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{
//!     let CommentedString(string, comments) = $value;
//!     let string = format!(concat!("{}{", $modif, "}"), string, $added);
//!     CommentedString(string, comments)
//! }}
//!
//! macro parse_comment($value:expr, $_modif:literal, $added:expr) {{
//!     let mut commented_string = $value;
//!     commented_string.1.push((commented_string.0.len(), $added.to_string()));
//!     commented_string
//! }}
//! ```
//!
//! ## Forced inlining
//!
//! You might be wondering: What are the `false` and `true` in the
//! second argument of [`format_like!`] used for?
//!
//! Well, they determine wether an argument _must_ be inlined (i.e. be
//! placed within the string like `{arg}`). This is useful when you
//! want to limit the types of arguments that a macro should handle.
//!
//! As you might have seen earlier, [`format_like!`] accepts member
//! access, like `{range.end}`. If you force a parameter to always be
//! placed inline, that limits the types of tokens your macro must be
//! able to handle, so you could rewrite the `parse_comment` macro to
//! be:
//!
//! ```rust
//! #![feature(decl_macro)]
//! macro parse_comment($value:expr, $modif:literal, $($identifier:ident).*) {{
//!     // innards
//! }}
//! ```
//!
//! While this may not seem useful, it comes with two interesting
//! abilities:
//!
//! 1 - If arguments must be inlined, you are allowed to leave the
//! pair empty, like `<>`, and you can handle this situation
//! differently if you want.
//! 2 - By accessing the `$identifiers` directly, you can manipulate
//! them in whichever way you want, heck, they may not even point to
//! any actual variable in the code, and could be some sort of
//! differently handled string literal.
//!
//! ## Motivation
//!
//! Even after reading all that, I wouldn't be surprised if you
//! haven't found any particular use for this crate, and that's fine.
//!
//! But here is what was _my_ motivation for creating it:
//!
//! In my _in development_ text editor [Duat], there _used to be_ a
//! `text` macro, which created a `Text` struct, which was essentially
//! a [`String`] with formatting `Tag`s added on to it.
//!
//! It used to work like this:
//!
//! ```rust,ignore
//! let text = text!("start " [RedColor.subvalue] variable " " other_variable " ");
//! ```
//!
//! This macro was a simple declarative macro, so while it was easy to
//! implement, there were several drawbacks to its design:
//!
//! - It was ignored by rustfmt;
//! - It didn't look like Rust;
//! - tree-sitter failed at syntax highlighting it;
//! - It didn't look like Rust;
//! - Way too much space was occupied by simple things like `" "`;
//! - It didn't look like Rust;
//!
//! And now I have replaced the old `text` macro with a new version,
//! based on `format_like!`, which makes for a much cleaner design:
//!
//! ```rust,ignore
//! let text = text!("start [RedColor.subvalue]{variable} {other_variable} ");
//! ```
//!
//! [`Display`]: std::fmt::Display
//! [Duat]: https://github.com/AhoyISki/duat
use std::ops::Range;

use litrs::StringLit;
use proc_macro::{Delimiter, Group, Ident, Literal, Punct, Spacing, Span, TokenStream, TokenTree};

/// A macro for creating format-like macros
///
/// ```rust
/// #![feature(decl_macro)]
/// use format_like::format_like;
///
/// #[derive(Debug, PartialEq)]
/// struct CommentedString(String, Vec<(usize, String)>);
///
/// let comment = "there is an error in this word";
/// let text = "text";
/// let range = 0..usize::MAX;
///
/// let commented_string = commented_string!(
///     "This is <comment>worng {}, and this is the end of the range {range.end}",
///     text
/// );
///
/// assert_eq!(
///     commented_string,
///     CommentedString(
///         "This is worng text, and this is the end of the range 18446744073709551615".to_string(),
///         vec![(8, "there is an error in this word".to_string())]
///     )
/// );
///
/// macro commented_string($($parts:tt)*) {
///     format_like!(
///         parse_str,
///         [('{', parse_interpolation, false), ('<', parse_comment, true)],
///         CommentedString(String::new(), Vec::new()),
///         $($parts)*
///     )
/// }
///
/// macro parse_str($value:expr, $str:literal) {{
///     let mut commented_string = $value;
///     commented_string.0.push_str($str);
///     commented_string
/// }}
///
/// macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{
///     let CommentedString(string, comments) = $value;
///     let string = format!(concat!("{}{", $modif, "}"), string, $added);
///     CommentedString(string, comments)
/// }}
///
/// macro parse_comment($value:expr, $_modif:literal, $added:expr) {{
///     let mut commented_string = $value;
///     commented_string.1.push((commented_string.0.len(), $added.to_string()));
///     commented_string
/// }}
/// ```
#[proc_macro]
pub fn format_like(input: TokenStream) -> TokenStream {
    let fmt_like = match FormatLike::parse(input.into_iter()) {
        Ok(fmt_like) => fmt_like,
        Err(err) => return err,
    };

    let str = fmt_like.str.value();
    let arg_parsers = &fmt_like.arg_parsers;

    let mut args = Vec::new();

    let mut arg: Option<CurrentArg> = None;
    let mut unescaped_rhs: Option<(usize, char)> = None;
    let mut push_new_ident = true;
    let mut positional_needed = 0;

    let str_span = |_r: Range<usize>| fmt_like.str_span;

    for (i, char) in str.char_indices() {
        if let Some((j, p, mut idents, mut modif)) = arg.take() {
            let [lhs, rhs] = arg_parsers[p].delims;
            if char == rhs {
                let modif = match modif {
                    Some(range) => {
                        let str =
                            unsafe { str::from_utf8_unchecked(&str.as_bytes()[range.clone()]) };
                        let mut str = Literal::string(str);
                        str.set_span(fmt_like.str_span);

                        TokenStream::from(TokenTree::Literal(str))
                    }
                    None => TokenStream::from(TokenTree::Literal(Literal::string(""))),
                };

                if idents.is_empty() {
                    if arg_parsers[p].inline_only {
                        args.push(Arg::Inlined(p, TokenStream::new(), modif));
                    } else {
                        positional_needed += 1;
                        args.push(Arg::Positional(p, j..i + 1, modif));
                    }
                } else if push_new_ident {
                    return compile_err(
                        str_span(i - 1..i),
                        "invalid format string: field access expected an identifier",
                    );
                } else {
                    let mut stream = Vec::new();
                    let len = idents.len();

                    for (i, (range, is_tuple_member)) in idents.into_iter().enumerate() {
                        let str =
                            unsafe { str::from_utf8_unchecked(&str.as_bytes()[range.clone()]) };

                        stream.push(if is_tuple_member {
                            TokenTree::Literal({
                                let mut literal = Literal::usize_unsuffixed(str.parse().unwrap());
                                literal.set_span(str_span(range.clone()));
                                literal
                            })
                        } else {
                            TokenTree::Ident(Ident::new(str, str_span(range.clone())))
                        });

                        if i != len - 1 {
                            stream.push(TokenTree::Punct({
                                let mut punct = Punct::new('.', Spacing::Alone);
                                punct.set_span(str_span(range.end..range.end + 1));
                                punct
                            }));
                        }
                    }

                    args.push(Arg::Inlined(p, TokenStream::from_iter(stream), modif));
                }

                continue;
            } else if char == lhs && idents.is_empty() {
                // If arg was empty, that means the delimiter was repeated, so escape
                // it.
                extend_str_arg(&mut args, char, i - 1);
                continue;
            }

            // We might have mismatched delimiters
            if arg_parsers
                .iter()
                .any(|ap| char == ap.delims[0] || char == ap.delims[1])
            {
                return TokenStream::from_iter([
                    compile_err(
                        str_span(i..i + 1),
                        "invalid format string: wrong match for delimiter",
                    ),
                    compile_err(
                        str_span(j..j + 1),
                        format!("from this delimiter, expected {rhs}"),
                    ),
                ]);
            } else if char.is_alphanumeric() || char == '_' || modif.is_some() {
                if let Some(modif) = &mut modif {
                    modif.end = i + 1;
                } else if let Some((range, is_tuple_member)) = idents.last_mut()
                    && !push_new_ident
                {
                    *is_tuple_member &= char.is_ascii_digit();
                    range.end = i + 1;
                } else {
                    idents.push((i..i + 1, char.is_ascii_digit()));
                    push_new_ident = false;
                }
            } else if char == '.' {
                if let Some(modif) = &mut modif {
                    modif.end = i + 1;
                } else if push_new_ident {
                    // Can't start an identifier list with '.' or put multiple '.'s in a
                    // row.
                    return compile_err(
                        str_span(i..i + 1),
                        "invalid format string: unexpected '.' here",
                    );
                } else {
                    push_new_ident = true;
                }
            } else if char == ':' {
                if let Some(modif) = &mut modif {
                    modif.end = i + 1;
                } else {
                    modif = Some(i + 1..i + 1);
                }
            } else {
                return compile_err(
                    str_span(i..i + 1),
                    format!("invalid format string: unexpected {char} here"),
                );
            }

            arg = Some((j, p, idents, modif));
        } else if let Some(p) = arg_parsers
            .iter()
            .position(|ap| char == ap.delims[0] || char == ap.delims[1])
        {
            // If the char is a left delimiter, begin an argument.
            // If it is a right delimiter, handle dangling right parameter
            // scenarios.
            if char == arg_parsers[p].delims[0] {
                push_new_ident = true;
                arg = Some((i, p, Vec::new(), None));
            } else if let Some((j, unescaped)) = unescaped_rhs {
                // Double delimiters are escaped.
                if char == unescaped {
                    unescaped_rhs = None;
                    extend_str_arg(&mut args, char, i);
                } else {
                    return compile_err(
                        str_span(j..j + 1),
                        format!("invalid format string: unmatched {unescaped} found"),
                    );
                }
            } else {
                unescaped_rhs = Some((i, char));
            }
        } else if let Some((j, unescaped)) = unescaped_rhs {
            return compile_err(
                str_span(j..j + 1),
                format!("invalid format string: unmatched {unescaped} found"),
            );
        } else {
            extend_str_arg(&mut args, char, i);
        }
    }

    if let Some((i, unescaped)) = unescaped_rhs {
        return compile_err(
            str_span(i..i + 1),
            format!("invalid format string: unmatched {unescaped} found"),
        );
    }

    let mut token_stream = fmt_like.initial;

    let positional_provided = fmt_like.exprs.len();
    let mut exprs = fmt_like.exprs.into_iter();

    let comma = TokenTree::Punct(Punct::new(',', Spacing::Alone));

    for arg in args {
        token_stream = match arg {
            Arg::Str(string, range) => {
                let mut str = Literal::string(&string);
                str.set_span(str_span(range));

                recurse_parser(
                    &fmt_like.str_parser,
                    token_stream
                        .into_iter()
                        .chain([comma.clone(), TokenTree::Literal(str)]),
                )
            }
            Arg::Positional(p, range, modif) => {
                if let Some(expr) = exprs.next() {
                    recurse_parser(
                        &fmt_like.arg_parsers[p].parser,
                        token_stream
                            .into_iter()
                            .chain([comma.clone()])
                            .chain(modif)
                            .chain([comma.clone()])
                            .chain(expr),
                    )
                } else {
                    let npl = if positional_needed == 1 { "" } else { "s" };
                    let pverb = if positional_provided == 1 {
                        "is"
                    } else {
                        "are"
                    };
                    let ppl = if positional_provided == 1 { "" } else { "s" };

                    return compile_err(
                        str_span(range),
                        format!(
                            "{positional_needed} positional argument{npl} in format string, but there {pverb} {positional_provided} argument{ppl}"
                        ),
                    );
                }
            }
            Arg::Inlined(p, idents, modif) => recurse_parser(
                &fmt_like.arg_parsers[p].parser,
                token_stream
                    .into_iter()
                    .chain([comma.clone()])
                    .chain(modif)
                    .chain([comma.clone()])
                    .chain(idents),
            ),
        }
    }

    // There should be no positional arguments left.
    if let Some(expr) = exprs.next() {
        return compile_err(
            expr.into_iter().next().unwrap().span(),
            "argument never used",
        );
    }

    token_stream
}

struct ArgParser {
    delims: [char; 2],
    delim_span: Span,
    parser: Ident,
    inline_only: bool,
}

struct FormatLike {
    str_parser: Ident,
    arg_parsers: Vec<ArgParser>,
    initial: TokenStream,
    str: StringLit<String>,
    str_span: Span,
    exprs: Vec<TokenStream>,
}

impl FormatLike {
    fn parse(mut stream: impl Iterator<Item = TokenTree>) -> Result<Self, TokenStream> {
        use TokenTree as TT;

        let str_parser = get_ident(stream.next())?;

        consume_comma(stream.next())?;

        let arg_parsers = {
            let group = match stream.next() {
                Some(TT::Group(group)) if group.delimiter() == Delimiter::Bracket => group,
                Some(other) => return Err(compile_err(other.span(), "expected a list")),
                _ => return Err(compile_err(Span::mixed_site(), "expected a list")),
            };

            let mut arg_parsers = Vec::new();

            let mut stream = group.stream().into_iter();

            loop {
                static INVALID_ERR: &str = "expected one of '{', '(', '[', or '<'";

                let group = match stream.next() {
                    Some(TT::Group(group)) if group.delimiter() == Delimiter::Parenthesis => group,
                    None => break,
                    Some(other) => return Err(compile_err(other.span(), "expected a tuple")),
                };

                let mut substream = group.stream().into_iter();

                let (delims, delim_span) = match substream.next() {
                    Some(TT::Literal(literal)) => match literal.to_string().as_str() {
                        "'{'" => (['{', '}'], literal.span()),
                        "'('" => (['(', ')'], literal.span()),
                        "'['" => (['[', ']'], literal.span()),
                        "'<'" => (['<', '>'], literal.span()),
                        _ => return Err(compile_err(literal.span(), INVALID_ERR)),
                    },
                    Some(other) => return Err(compile_err(other.span(), INVALID_ERR)),
                    _ => return Err(compile_err(Span::mixed_site(), INVALID_ERR)),
                };

                consume_comma(substream.next())?;

                let parser = get_ident(substream.next())?;

                consume_comma(substream.next())?;

                let inline_only = match substream.next() {
                    Some(TT::Ident(ident)) => match ident.to_string().as_str() {
                        "true" => true,
                        "false" => false,
                        _ => {
                            return Err(compile_err(
                                ident.span(),
                                format!("expected a bool, got {ident:?}"),
                            ));
                        }
                    },
                    Some(other) => {
                        return Err(compile_err(
                            other.span(),
                            format!("expected a bool, got {other}"),
                        ));
                    }
                    _ => return Err(compile_err(Span::mixed_site(), "expected a bool")),
                };

                arg_parsers.push(ArgParser { delims, delim_span, parser, inline_only });

                _ = consume_comma(stream.next());
            }

            arg_parsers
        };

        if let Some((lhs, rhs)) = arg_parsers.iter().enumerate().find_map(|(i, lhs)| {
            arg_parsers.iter().enumerate().find_map(|(j, rhs)| {
                (i != j)
                    .then(|| (rhs.delims == lhs.delims).then_some((lhs, rhs)))
                    .flatten()
            })
        }) {
            return Err(TokenStream::from_iter([
                compile_err(lhs.delim_span, "this delimiter"),
                compile_err(rhs.delim_span, "is the same as this"),
            ]));
        }

        consume_comma(stream.next())?;

        let initial = {
            let mut initial = Vec::new();

            for token in stream.by_ref() {
                if let TokenTree::Punct(punct) = &token
                    && punct.as_char() == ','
                {
                    break;
                }

                initial.push(token);
            }

            TokenStream::from_iter(initial)
        };

        let (str, str_span) = match stream.next() {
            Some(TokenTree::Literal(literal)) => {
                match litrs::StringLit::parse(literal.to_string()) {
                    Ok(str) => (str, literal.span()),
                    Err(_) => return Err(compile_err(literal.span(), "expected a string literal")),
                }
            }
            Some(other) => return Err(compile_err(other.span(), "expected a string literal")),
            None => return Err(compile_err(Span::mixed_site(), "expected a string literal")),
        };

        let exprs = match stream.next() {
            Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => {
                let mut exprs = Vec::new();

                let mut tokens = Vec::new();

                for token in stream {
                    if let TokenTree::Punct(punct) = &token
                        && punct.as_char() == ','
                    {
                        if !tokens.is_empty() {
                            exprs.push(TokenStream::from_iter(tokens.drain(..)));
                        }
                    } else {
                        tokens.push(token);
                    }
                }

                if !tokens.is_empty() {
                    exprs.push(TokenStream::from_iter(tokens));
                }

                exprs
            }
            Some(other) => return Err(compile_err(other.span(), "expected a comma")),
            None => Vec::new(),
        };

        Ok(Self {
            str_parser,
            arg_parsers,
            initial,
            str,
            str_span,
            exprs,
        })
    }
}

enum Arg {
    Str(String, Range<usize>),
    Positional(usize, Range<usize>, TokenStream),
    Inlined(usize, TokenStream, TokenStream),
}

fn recurse_parser(parser: &Ident, stream: impl Iterator<Item = TokenTree>) -> TokenStream {
    let start = parser.span().start();

    TokenStream::from_iter([
        TokenTree::Ident(parser.clone()),
        TokenTree::Punct({
            let mut punct = Punct::new('!', Spacing::Alone);
            punct.set_span(start);
            punct
        }),
        TokenTree::Group(Group::new(Delimiter::Parenthesis, stream.collect())),
    ])
}

fn consume_comma(value: Option<TokenTree>) -> Result<(), TokenStream> {
    match value {
        Some(TokenTree::Punct(punct)) if punct.as_char() == ',' => Ok(()),
        Some(other) => Err(compile_err(other.span(), "Expected a comma")),
        _ => Err(compile_err(Span::mixed_site(), "Expected a comma")),
    }
}

fn get_ident(value: Option<TokenTree>) -> Result<Ident, TokenStream> {
    match value {
        Some(TokenTree::Ident(ident)) => Ok(ident),
        Some(other) => Err(compile_err(other.span(), "Expected an identifier")),
        _ => Err(compile_err(Span::mixed_site(), "Expected an identifier")),
    }
}

fn extend_str_arg(args: &mut Vec<Arg>, char: char, i: usize) {
    if let Some(Arg::Str(string, range)) = args.last_mut() {
        string.push(char);
        range.end = i + 1;
    } else {
        args.push(Arg::Str(String::from(char), i..i + 1))
    }
}

fn compile_err(span: Span, msg: impl std::fmt::Display) -> TokenStream {
    let (start, end) = (span.start(), span.end());

    TokenStream::from_iter([
        TokenTree::Punct({
            let mut punct = Punct::new(':', Spacing::Joint);
            punct.set_span(start);
            punct
        }),
        TokenTree::Punct({
            let mut punct = Punct::new(':', Spacing::Alone);
            punct.set_span(start);
            punct
        }),
        TokenTree::Ident(Ident::new("core", start)),
        TokenTree::Punct({
            let mut punct = Punct::new(':', Spacing::Joint);
            punct.set_span(start);
            punct
        }),
        TokenTree::Punct({
            let mut punct = Punct::new(':', Spacing::Alone);
            punct.set_span(start);
            punct
        }),
        TokenTree::Ident({
            let mut ident = Ident::new("compile_error", start);
            ident.set_span(start);
            ident
        }),
        TokenTree::Punct({
            let mut punct = Punct::new('!', Spacing::Alone);
            punct.set_span(start);
            punct
        }),
        TokenTree::Group({
            let mut group = Group::new(Delimiter::Brace, {
                TokenStream::from_iter([TokenTree::Literal({
                    let mut string = Literal::string(&msg.to_string());
                    string.set_span(end);
                    string
                })])
            });
            group.set_span(end);
            group
        }),
    ])
}

type CurrentArg = (
    usize,
    usize,
    Vec<(Range<usize>, bool)>,
    Option<Range<usize>>,
);
