# format-like ![License: AGPL-3.0-or-later](https://img.shields.io/badge/license-AGPL--3.0--or--later-blue) [![format-like on crates.io](https://img.shields.io/crates/v/format-like)](https://crates.io/crates/format-like) [![format-like on docs.rs](https://docs.rs/format-like/badge.svg)](https://docs.rs/format-like)

A macro for creating format-like macros

Have you ever wanted to emulate the functionality of the `format!`
family of macros, but with an output that is not a [`String`][__link0] or
something built from a [`String`][__link1]?

No?

Well, still, this might still be interesting for you.

`format-like` aims to let *you* decide how to interpret what is
inside `{}` pairs, instead of calling something like
`std::fmt::Display::fmt(&value)`.

Additionaly, it lets you create 3 other types of bracket pairs:
`()`, `[]` and `<>`, so you can interpret things in even more
ways! This does of course come with the regular escaping that the
[`format!`][__link2] macro does, so `{{` is escaped to just `{`, the same
being the case for the other delimiters as well.

Here’s how it works:

```rust
use format_like::format_like;

struct CommentedString(String, Vec<(usize, String)>);

let comment = "there is an error in this word";
let text = "text";
let range = 0..usize::MAX;

let commented_string = format_like!(
    parse_str,
    [('{', parse_interpolation, false), ('<', parse_comment, true)],
    CommentedString(String::new(), Vec::new()),
    "This is <comment>regluar {}, interpolated and commented {range.end}",
    text
);
```

In this example, the `{}` should work as intended, but you also
have access to `<>` interpolation. Inside `<>`, a comment will be
added, with the associated `usize` being its position in the
[`String`][__link3].

This will all be done through the `parse_str`,
`parse_interpolation` and `parse_comment` macros:

```rust
#![feature(decl_macro)]
macro parse_str($value:expr, $str:literal) {{
    let mut commented_string = $value;
    commented_string.0.push_str($str);
    commented_string
}}

macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{
    let CommentedString(string, comments) = $value;
    let string = format!(concat!("{}{", $modif, "}"), string, $added);
    CommentedString(string, comments)
}}

macro parse_comment($value:expr, $_modif:literal, $added:expr) {{
    let mut commented_string = $value;
    commented_string
        .1
        .push((commented_string.0.len(), $added.to_string()));
    commented_string
}}
```

The `parse_str` macro will be responsible for handling the non
`{}` or `<>` parts of the literal `&str`. The `parse_comment` and
`parse_interpolation` methods will handle what’s inside the `<>`
and `{}` pairs, respectively.

`parse_comment` and `parse_interpolation` must have three
parameters, one for the `value` being modified (in this case, a
`CommentedString`), one for the modifier (`"?", "#?", ".3", etc), which might come after a `“:”` in the pair. and one for the object being added (it's [`Display\`\] objects in this case, but
it could be anything else).

Now, as I mentioned earlier, this crate is meant for you to create
*your own* format like macros, so you should package all of this
up into a single macro, like this:

```rust
#![feature(decl_macro)]
use format_like::format_like;

#[derive(Debug, PartialEq)]
struct CommentedString(String, Vec<(usize, String)>);

let comment = "there is an error in this word";
let text = "text";
let range = 0..usize::MAX;

let commented_string = commented_string!(
    "This is <comment>regluar {}, interpolated and commented {range.end}",
    text
);

assert_eq!(
    commented_string,
    CommentedString(
        "This is regluar text, interpolated and commented 18446744073709551615".to_string(),
        vec![(8, "there is an error in this word".to_string())]
    )
);

macro commented_string($($parts:tt)*) {
    format_like!(
        parse_str,
        [('{', parse_interpolation, false), ('<', parse_comment, true)],
        CommentedString(String::new(), Vec::new()),
        $($parts)*
    )
}

macro parse_str($value:expr, $str:literal) {{
    let mut commented_string = $value;
    commented_string.0.push_str($str);
    commented_string
}}

macro parse_interpolation($value:expr, $modif:literal, $added:expr) {{
    let CommentedString(string, comments) = $value;
    let string = format!(concat!("{}{", $modif, "}"), string, $added);
    CommentedString(string, comments)
}}

macro parse_comment($value:expr, $_modif:literal, $added:expr) {{
    let mut commented_string = $value;
    commented_string.1.push((commented_string.0.len(), $added.to_string()));
    commented_string
}}
```

### Forced inlining

You might be wondering: What are the `false` and `true` in the
second argument of [`format_like!`][__link4] used for?

Well, they determine wether an argument *must* be inlined (i.e. be
placed within the string like `{arg}`). This is useful when you
want to limit the types of arguments that a macro should handle.

As you might have seen earlier, [`format_like!`][__link5] accepts member
access, like `{range.end}`. If you force a parameter to always be
placed inline, that limits the types of tokens your macro must be
able to handle, so you could rewrite the `parse_comment` macro to
be:

```rust
#![feature(decl_macro)]
macro parse_comment($value:expr, $modif:literal, $($identifier:ident).*) {{
    // innards
}}
```

While this may not seem useful, it comes with two interesting
abilities:

1 - If arguments must be inlined, you are allowed to leave the
pair empty, like `<>`, and you can handle this situation
differently if you want.
2 - By accessing the `$identifiers` directly, you can manipulate
them in whichever way you want, heck, they may not even point to
any actual variable in the code, and could be some sort of
differently handled string literal.

### Motivation

Even after reading all that, I wouldn’t be surprised if you
haven’t found any particular use for this crate, and that’s fine.

But here is what was *my* motivation for creating it:

In my *in development* text editor [Duat][__link6], there *used to be* a
`text` macro, which created a `Text` struct, which was essentially
a [`String`][__link7] with formatting `Tag`s added on to it.

It used to work like this:

```rust
let text = text!("start " [RedColor.subvalue] variable " " other_variable " ");
```

This macro was a simple declarative macro, so while it was easy to
implement, there were several drawbacks to its design:

* It was ignored by rustfmt;
* It didn’t look like Rust;
* tree-sitter failed at syntax highlighting it;
* It didn’t look like Rust;
* Way too much space was occupied by simple things like `" "`;
* It didn’t look like Rust;

And now I have replaced the old `text` macro with a new version,
based on `format_like!`, which makes for a much cleaner design:

```rust
let text = text!("start [RedColor.subvalue]{variable} {other_variable} ");
```


 [__link0]: https://doc.rust-lang.org/stable/std/string/struct.String.html
 [__link1]: https://doc.rust-lang.org/stable/std/string/struct.String.html
 [__link2]: https://doc.rust-lang.org/stable/std/macro.format.html
 [__link3]: https://doc.rust-lang.org/stable/std/string/struct.String.html
 [__link4]: `format_like!`
 [__link5]: `format_like!`
 [__link6]: https://github.com/AhoyISki/duat
 [__link7]: https://doc.rust-lang.org/stable/std/string/struct.String.html
