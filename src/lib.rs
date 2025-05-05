use std::ops::Range;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote};
use syn::{
    Expr, Ident, LitBool, LitChar, LitStr, Path, Token, bracketed, parenthesized,
    parse::{Parse, ParseBuffer},
    parse_macro_input,
    spanned::Spanned,
};

struct ArgParser {
    delims: (LitChar, char),
    parser: Path,
    inline_only: bool,
}

impl ArgParser {
    fn new(input: &ParseBuffer) -> syn::Result<Self> {
        const VALID_DELIMS: &[[char; 2]] = &[['{', '}'], ['(', ')'], ['[', ']'], ['<', '>']];
        let elems;
        parenthesized!(elems in input);

        let delims = {
            let left: LitChar = elems.parse()?;

            if let Some([_, right]) = VALID_DELIMS.iter().find(|[rhs, _]| left.value() == *rhs) {
                (left, *right)
            } else {
                return Err(syn::Error::new_spanned(left, "is not a valid delimiter"));
            }
        };

        elems.parse::<Token![,]>()?;
        let parser = elems.parse()?;
        elems.parse::<Token![,]>()?;
        let inline_only = elems.parse::<LitBool>()?.value();

        Ok(Self {
            delims,
            parser,
            inline_only,
        })
    }
}

struct FormatLike {
    str_parser: Path,
    arg_parsers: Vec<ArgParser>,
    initial: Expr,
    str: LitStr,
    exprs: Vec<Expr>,
}

impl Parse for FormatLike {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let str_parser = input.parse()?;
        input.parse::<Token![,]>()?;

        let arg_parsers: Vec<ArgParser> = {
            let arg_parsers;
            bracketed!(arg_parsers in input);
            arg_parsers
                .parse_terminated(ArgParser::new, Token![,])?
                .into_iter()
                .collect()
        };

        if let Some((lhs, rhs)) = arg_parsers.iter().enumerate().find_map(|(i, lhs)| {
            arg_parsers.iter().enumerate().find_map(|(j, rhs)| {
                (i != j)
                    .then(|| (rhs.delims.1 == lhs.delims.1).then_some((lhs, rhs)))
                    .flatten()
            })
        }) {
            let l_err = syn::Error::new_spanned(&lhs.delims.0, "this delimiter");
            let mut r_err = syn::Error::new_spanned(&rhs.delims.0, "is the same as this");
            r_err.combine(l_err);
            return Err(r_err);
        }
        input.parse::<Token![,]>()?;

        let initial = input.parse()?;
        input.parse::<Token![,]>()?;

        let str = input.parse()?;

        let exprs = if !input.is_empty() {
            input.parse::<Token![,]>()?;
            input
                .parse_terminated(Expr::parse, Token![,])?
                .into_iter()
                .collect()
        } else {
            Vec::new()
        };

        Ok(Self {
            str_parser,
            arg_parsers,
            initial,
            str,
            exprs,
        })
    }
}

#[proc_macro]
pub fn format_like(input: TokenStream) -> TokenStream {
    let fmt_like = parse_macro_input!(input as FormatLike);
    let lit_str = &fmt_like.str;
    let str = lit_str.value();
    let arg_parsers = &fmt_like.arg_parsers;

    let mut args = Vec::new();

    let mut arg: Option<CurrentArg> = None;
    let mut unescaped_rhs: Option<(usize, char)> = None;
    let mut push_new_ident = true;
    let mut positional_needed = 0;

    let str_span = |r: Range<usize>| lit_str.token().subspan(r.start + 1..r.end + 1).unwrap();

    for (i, char) in str.char_indices() {
        if let Some((j, p, mut idents, mut modif)) = arg.take() {
            let (lhs, rhs) = &arg_parsers[p].delims;
            if char == *rhs {
                let modif = match modif {
                    Some(range) => {
                        let str =
                            unsafe { str::from_utf8_unchecked(&str.as_bytes()[range.clone()]) };
                        let str = LitStr::new(str, str_span(range));

                        quote! { #str }
                    }
                    None => quote! { "" },
                };

                if idents.is_empty() {
                    if arg_parsers[p].inline_only {
                        args.push(Arg::Inlined(p, Vec::new(), modif));
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
                    let idents = idents
                        .into_iter()
                        .map(|range| {
                            let mut ident = format_ident!("{}", unsafe {
                                str::from_utf8_unchecked(&str.as_bytes()[range.clone()])
                            });
                            ident.set_span(str_span(range));
                            ident
                        })
                        .collect();

                    args.push(Arg::Inlined(p, idents, modif));
                }

                continue;
            } else if char == lhs.value() && idents.is_empty() {
                // If arg was empty, that means the delimiter was repeated, so escape it.
                extend_str_arg(&mut args, i);
                continue;
            }

            // We might have mismatched delimiters
            if arg_parsers
                .iter()
                .any(|ap| char == ap.delims.0.value() || char == ap.delims.1)
            {
                let mut err = syn::Error::new(
                    str_span(i..i + 1),
                    "invalid format string: wrong match for delimiter",
                );
                err.combine(syn::Error::new(
                    str_span(j..j + 1),
                    format!("from this delimiter, expected {rhs}"),
                ));
                let compile_err = err.into_compile_error();

                // Since this should return an Expr, we need to brace it.
                let err = quote! {{
                    #compile_err
                }};

                return err.into();
            } else if char.is_alphanumeric() || char == '_' || modif.is_some() {
                if let Some(modif) = &mut modif {
                    modif.end = i + 1;
                } else if let Some(last) = idents.last_mut()
                    && !push_new_ident
                {
                    last.end = i + 1;
                } else {
                    idents.push(i..i + 1);
                    push_new_ident = false;
                }
            } else if char == '.' {
                if let Some(modif) = &mut modif {
                    modif.end = i + 1;
                } else if push_new_ident {
                    // Can't start an identifier list with '.' or put multiple '.'s in a row.
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
            .position(|ap| char == ap.delims.0.value() || char == ap.delims.1)
        {
            // If the char is a left delimiter, begin an argument.
            // If it is a right delimiter, handle dangling right parameter scenarios.
            if char == arg_parsers[p].delims.0.value() {
                push_new_ident = true;
                arg = Some((i, p, Vec::new(), None));
            } else if let Some((j, unescaped)) = unescaped_rhs {
                // Double delimiters are escaped.
                if char == unescaped {
                    unescaped_rhs = None;
                    extend_str_arg(&mut args, i);
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
            extend_str_arg(&mut args, i);
        }
    }

    if let Some((i, unescaped)) = unescaped_rhs {
        return compile_err(
            str_span(i..i + 1),
            format!("invalid format string: unmatched {unescaped} found"),
        );
    }

    let expr = fmt_like.initial;
    let mut token_stream = quote! { #expr };

    let positional_provided = fmt_like.exprs.len();
    let mut exprs = fmt_like.exprs.into_iter();

    for arg in args {
        token_stream = match arg {
            Arg::Str(range) => {
                let str = unsafe { str::from_utf8_unchecked(&str.as_bytes()[range.clone()]) };
                let str = LitStr::new(str, str_span(range));
                let parser = &fmt_like.str_parser;

                quote! {
                    #parser!(#token_stream, #str)
                }
            }
            Arg::Positional(p, range, modif) => {
                if let Some(expr) = exprs.next() {
                    let parser = &fmt_like.arg_parsers[p].parser;

                    quote! {
                        #parser!(#token_stream, #expr, #modif)
                    }
                } else {
                    let npl = if positional_needed == 1 { "" } else { "s" };
                    let pverb = if positional_provided == 1 { "is" } else { "are" };
                    let ppl = if positional_provided == 1 { "" } else { "s" };

                    return compile_err(
                        str_span(range),
                        format!(
                            "{positional_needed} positional argument{npl} in format string, but there {pverb} {positional_provided} argument{ppl}"
                        ),
                    );
                }
            }
            Arg::Inlined(p, idents, modif) => {
                let parser = &fmt_like.arg_parsers[p].parser;

                quote! {
                    #parser!(#token_stream, #(#idents).*, #modif)
                }
            }
        }
    }

    // There should be no positional arguments left.
    if let Some(expr) = exprs.next() {
        return compile_err(expr.span(), "argument never used");
    }

    token_stream.into()
}

enum Arg {
    Str(Range<usize>),
    Positional(usize, Range<usize>, proc_macro2::TokenStream),
    Inlined(usize, Vec<Ident>, proc_macro2::TokenStream),
}

fn extend_str_arg(args: &mut Vec<Arg>, start_of_char: usize) {
    if let Some(Arg::Str(range)) = args.last_mut() {
        range.end = start_of_char + 1;
    } else {
        args.push(Arg::Str(start_of_char..start_of_char + 1))
    }
}

fn compile_err(span: Span, msg: impl std::fmt::Display) -> TokenStream {
    let compile_err = syn::Error::new(span, msg).into_compile_error();

    let err = quote! {{
        #compile_err
    }};

    err.into()
}

type CurrentArg = (usize, usize, Vec<Range<usize>>, Option<Range<usize>>);
