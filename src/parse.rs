use std::fmt;
use std::result;

use utf8::{self, Char};

// BREADCRUMBS:
//
// Don't worry about the performance of the parser.
//
// Start by parsing the structure as faithfully as possible. Don't try to
// flatten anything during parsing. Parsing should however bake in the concept
// of "flexibility."
//
// Once parsed, there should be a way to convert that structure into a
// sequence of flattened globs, i.e., globs that have no alternations
// whatsoever.
//
// Once you have a sequence of flattened globs, it should be pretty
// straight-forward to split each of those globs into directory components
// based on where literal directory separators occur. Each of these components
// can then be compiled into their own distinct globs.
//
// But don't forget to test edge cases, particularly around absolute paths
// on Windows.

pub type Result<T> = std::result::Result<T, ParseError>;

#[derive(Clone, Debug)]
pub enum ParseError {}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {}
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Glob {
    hir: Hir,
    recursive: bool,
    slash_wildcard: bool,
}

impl Glob {
    fn is_separator(&self, conf: &Config) -> bool {
        self.hir.is_separator(conf)
    }

    fn char(ch: Char) -> Glob {
        match ch {
            Char::Byte(byte) => Glob::byte(byte),
            Char::Codepoint(cp) => Glob::codepoint(cp),
        }
    }

    fn byte(byte: u8) -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Byte(byte)),
            recursive: false,
            slash_wildcard: false,
        }
    }

    fn byte_ranges(conf: &Config, ranges: Vec<(u8, u8)>) -> Glob {
        let slash_wildcard =
            ranges.iter().any(|&(s, e)| conf.contains_separator_byte(s, e));
        Glob {
            hir: Hir::Flat(HirFlat::ByteRanges(ranges)),
            recursive: false,
            slash_wildcard,
        }
    }

    fn codepoint(ch: char) -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Codepoint(ch)),
            recursive: false,
            slash_wildcard: false,
        }
    }

    fn codepoint_ranges(conf: &Config, ranges: Vec<(char, char)>) -> Glob {
        let slash_wildcard = ranges
            .iter()
            .any(|&(s, e)| conf.contains_separator_codepoint(s, e));
        Glob {
            hir: Hir::Flat(HirFlat::CodepointRanges(ranges)),
            recursive: false,
            slash_wildcard,
        }
    }

    fn any_one() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Any(HirAny::One)),
            recursive: false,
            slash_wildcard: true,
        }
    }

    fn any_one_no_separator() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Any(HirAny::OneNoSeparator)),
            recursive: false,
            slash_wildcard: false,
        }
    }

    fn any_many() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Any(HirAny::Many)),
            recursive: false,
            slash_wildcard: true,
        }
    }

    fn any_many_no_separator() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Any(HirAny::ManyNoSeparator)),
            recursive: false,
            slash_wildcard: false,
        }
    }

    fn recursive_prefix() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Recursive(HirRecursive::Prefix)),
            recursive: true,
            slash_wildcard: false,
        }
    }

    fn recursive_suffix() -> Glob {
        Glob {
            hir: Hir::Flat(HirFlat::Recursive(HirRecursive::Suffix)),
            recursive: true,
            slash_wildcard: false,
        }
    }

    fn concat(mut hirs: Vec<Glob>) -> Glob {
        if hirs.len() == 1 {
            return hirs.pop().unwrap();
        }
        let recursive = hirs.iter().any(|hir| hir.recursive);
        let slash_wildcard = hirs.iter().any(|hir| hir.slash_wildcard);
        Glob { hir: Hir::Concat(hirs), recursive, slash_wildcard }
    }

    fn alternate(mut hirs: Vec<Glob>) -> Glob {
        if hirs.len() == 1 {
            return hirs.pop().unwrap();
        }
        let recursive = hirs.iter().any(|hir| hir.recursive);
        let slash_wildcard = hirs.iter().any(|hir| hir.slash_wildcard);
        Glob { hir: Hir::Alternate(hirs), recursive, slash_wildcard }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Hir {
    Flat(HirFlat),
    Concat(Vec<Glob>),
    Alternate(Vec<Glob>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirFlat {
    Byte(u8),
    ByteRanges(Vec<(u8, u8)>),
    Codepoint(char),
    CodepointRanges(Vec<(char, char)>),
    Any(HirAny),
    Recursive(HirRecursive),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirAny {
    One,
    OneNoSeparator,
    Many,
    ManyNoSeparator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HirRecursive {
    Prefix, // **/ -> ([^/]*/)*, e.g., `a/**/b` and `**/b`
    Suffix, // /** -> (/[^/]*)*, e.g., `a/**`
}

impl Hir {
    fn is_separator(&self, conf: &Config) -> bool {
        match *self {
            Hir::Flat(ref flat) => flat.is_separator(conf),
            _ => false,
        }
    }
}

impl HirFlat {
    fn is_separator(&self, conf: &Config) -> bool {
        match *self {
            HirFlat::Byte(byte) => conf.is_separator_byte(byte),
            HirFlat::Codepoint(cp) => conf.is_separator_codepoint(cp),
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Parser {
    /// The configuration of this parser, as given by the caller.
    config: Config,
    /// A stack of nested alternating glob expressions. This is only non-empty
    /// where there exists a `{a,b,...,z}` in the glob.
    ///
    /// The outer Vec corresponds to the nesting depth of the alternation.
    /// e.g., for `{{a,b},c}`, then `alternate_stack.len() == 2` when parsing
    /// `a` and `b`. The inner vec represents the alternation itself. e.g.,
    /// for `{a,b,c}`, `alternate_stack.len() == 1` and
    /// `alternate_stack[0].len() == 3` immediately after parsing the second
    /// `,`.
    alternate_stack: Vec<Vec<Glob>>,
}

#[derive(Clone, Debug)]
pub struct Config {
    pub flexible: bool,
    pub case_insensitive: bool,
    /// Whether to interpret \ as a path separator.
    ///
    /// Currently, this is only enabled on Windows and is not tweakable as part
    /// of the public API. Namely, this is currently only used for testing such
    /// that we don't have any platform specific behavior in the glob parser
    /// itself. But rather, any platform specific behavior is parameterizable.
    pub backslash_separator: bool,
    /// Whether to treat \ as a way to escape glob meta characters. This is
    /// enabled by default on Unix and disabled by default on Windows. Namely,
    /// since Windows uses \ as a path separator, it is often convenient to
    /// just treat \ as a literal. Otherwise \\ is necessary to write a path
    /// separator.
    pub backslash_escape: bool,
    pub literal_separator: bool,
    pub literal_leading_dot: bool,
    pub allow_alternates: bool,
    pub allow_recursive: bool,
}

impl Default for Config {
    fn default() -> Config {
        Config {
            flexible: false,
            case_insensitive: false,
            backslash_escape: !cfg!(windows),
            backslash_separator: cfg!(windows),
            literal_separator: true,
            literal_leading_dot: true,
            allow_alternates: true,
            allow_recursive: true,
        }
    }
}

impl Config {
    fn is_separator_char(&self, ch: Char) -> bool {
        match ch {
            Char::Codepoint(cp) => self.is_separator_codepoint(cp),
            Char::Byte(byte) => self.is_separator_byte(byte),
        }
    }

    fn is_separator_codepoint(&self, cp: char) -> bool {
        cp.is_ascii() && self.is_separator_byte(cp as u8)
    }

    fn is_separator_byte(&self, b: u8) -> bool {
        b == b'/' || (self.backslash_separator && b == b'\\')
    }

    fn contains_separator_codepoint(&self, start: char, end: char) -> bool {
        if start <= '/' && '/' <= end {
            return true;
        }
        if self.backslash_separator && start <= '\\' && '\\' <= end {
            return true;
        }
        false
    }

    fn contains_separator_byte(&self, start: u8, end: u8) -> bool {
        if start <= b'/' && b'/' <= end {
            return true;
        }
        if self.backslash_separator && start <= b'\\' && b'\\' <= end {
            return true;
        }
        false
    }
}

impl Parser {
    pub fn new(config: Config) -> Parser {
        Parser { config, alternate_stack: vec![] }
    }

    pub fn parse(&mut self, pattern: &[u8]) -> Result<Glob> {
        ParserI { p: self, pattern, offset: 0 }.parse()
    }
}

#[derive(Debug)]
struct ParserI<'p> {
    p: &'p mut Parser,
    pattern: &'p [u8],
    offset: usize,
}

impl<'p> ParserI<'p> {
    fn parse(&mut self) -> Result<Glob> {
        let mut concat = vec![];
        loop {
            if self.is_eof() {
                break;
            }
            let cp = match self.char() {
                Char::Codepoint(cp) => cp,
                Char::Byte(byte) => {
                    // We only get a byte from UTF-8 decoding when there is
                    // invalid UTF-8. Since all glob meta characters are valid
                    // UTF-8, it follows that all invalid UTF-8 bytes are not
                    // glob meta characters. Thus, we treat them as literals.
                    concat.push(Glob::byte(byte));
                    self.bump();
                    continue;
                }
            };
            match cp {
                '?' => concat.push(self.parse_any_one()),
                '*' => self.parse_any_many(&mut concat),
                '\\' => self.parse_backslash(&mut concat),
                cp => {
                    if self.p.config.is_separator_codepoint(cp) {
                        self.parse_separator(cp, &mut concat);
                    } else {
                        concat.push(Glob::codepoint(cp));
                        self.bump();
                    }
                }
            }
        }
        Ok(Glob::concat(concat))
    }

    /// Parses a `?` wild-card. This assumes the parser is currently pointed at
    /// a `?`. After returning, the parser is pointed at the following byte.
    fn parse_any_one(&mut self) -> Glob {
        let glob = if self.p.config.literal_separator {
            Glob::any_one_no_separator()
        } else {
            Glob::any_one()
        };
        self.bump();
        glob
    }

    /// Parses a `*` wildcard, or possibly, a `**/` recursive wildcard.
    /// This assumes the parser is currently pointed at a `*` that has not
    /// been parsed yet. After returning, the parser is pointed at the byte
    /// following the `*`, or `**/` in the case of a recursive wildcard.
    ///
    /// N.B. Other forms of recursive wildcards are handled when parsing the
    /// path separator since all other such forms require a separator to
    /// precede the `**`.
    fn parse_any_many(&mut self, concat: &mut Vec<Glob>) {
        let litsep = self.p.config.literal_separator;
        let star = || {
            if litsep {
                Glob::any_many_no_separator()
            } else {
                Glob::any_many()
            }
        };
        // If recursive globs aren't allowed, then we're done immediately
        // without any additional checking, since all checking below is to
        // handle recursive globs.
        if !self.p.config.allow_recursive {
            concat.push(star());
            return;
        }
        // We have a `*` that either ends the glob or is NOT followed by a `*`.
        if !self.bump() || self.char() != '*' {
            concat.push(star());
            return;
        }
        // We have a `**` that either ends the glob or is NOT followed by a
        // `/`. Note that this cannot include `/**` since that case is always
        // handled when parsing the separator. This case only catches syntax
        // like `a**b` where `a` and `b` are _anything_ other than separators.
        // Thus, it isn't a recursive glob but just two stars.
        if !self.bump() || !self.p.config.is_separator_char(self.char()) {
            concat.push(star());
            concat.push(star());
            return;
        }
        // At this point, we have consumed a `**` and know that the subsequent
        // character is a separator. The only thing left to do is to confirm
        // that nothing precedes it (i.e., it is the start of a glob or a
        // nested glob inside an alternation). If anything precedes it, then it
        // is either not a recursive glob (e.g., `a**`) or is handled when
        // parsing a separator (e.g., `/**`). Thus, the only thing we handle
        // here is `**/`.
        if !concat.is_empty() {
            // We haven't consumed the trailing separator yet, so we leave that
            // to be handled normally.
            concat.push(star());
            concat.push(star());
            return;
        }
        // Gobble up the trailing `/`, which is part of the recursive prefix.
        self.bump();
        concat.push(Glob::recursive_prefix());
    }

    /// Parses a path separator, and, optionally, any recursive wildcards
    /// following the path separator.
    ///
    /// This assumes the parser is positioned at the separator. After
    /// returning, the parser will be positioned immediately following the
    /// separator or the subsequent recursive wildcard, if one is found.
    fn parse_separator(&mut self, sep: char, concat: &mut Vec<Glob>) {
        if !self.bump() {
            concat.push(Glob::codepoint(sep));
            return;
        }
        if !self.is_peek_recursive() {
            concat.push(Glob::codepoint(sep));
            return;
        }
        self.bump();
        self.bump();
        concat.push(Glob::recursive_suffix());
    }

    /// Parses a `\` in the glob. This assumes the parser is pointing at the
    /// `\`. After returning, the parser is pointing to the next character to
    /// be parsed.
    ///
    /// This handles a few different cases. If backslash escaping is enabled,
    /// then the `\` escapes the next character such that it is always treated
    /// as a literal. If backslash escaping is not enabled, then `\` is either
    /// treated as if it were a separator or as a literal, depending on the
    /// platform.
    fn parse_backslash(&mut self, concat: &mut Vec<Glob>) {
        let backsep = self.p.config.backslash_separator;
        if self.p.config.backslash_escape {
            if !self.bump() {
                concat.push(Glob::codepoint('\\'));
            } else if backsep && self.char() == '\\' {
                self.parse_separator('\\', concat);
            } else if self.char() == '/' {
                self.parse_separator('/', concat);
            } else {
                concat.push(Glob::char(self.char()));
                self.bump();
            }
        } else if backsep {
            self.parse_separator('\\', concat);
        } else {
            concat.push(Glob::codepoint('\\'));
            self.bump();
        }
    }

    /// Returns true if and only if the subsequent characters from the current
    /// position correspond to `**/` and any of its variations. i.e., `**\`,
    /// `**\\` or `**\/` depending on the configuration. This also returns
    /// true if the pattern ends with a `**`.
    ///
    /// If allow_recursive is disabled, then this always returns false.
    fn is_peek_recursive(&self) -> bool {
        if !self.p.config.allow_recursive {
            return false;
        }
        if self.char() != '*' || self.peek().map_or(true, |c| c != '*') {
            return false;
        }
        let c1 = match self.peek2() {
            None => return true,
            Some(c) => c,
        };
        if self.p.config.is_separator_char(c1) {
            return true;
        }
        // The only way we can have a trailing separator here is if it's
        // escaped.
        if !self.p.config.backslash_escape {
            return false;
        }
        let c2 = match self.peek3() {
            None => return false,
            Some(c) => c,
        };
        c1 == '\\' && self.p.config.is_separator_char(c2)
    }

    /// Bump the parser to the next character. If there is no next character,
    /// then this returns false (and continues returning false on all
    /// subsequent invocations).
    fn bump(&mut self) -> bool {
        if self.is_eof() {
            return false;
        }
        self.offset += self.char().len();
        self.offset() < self.pattern().len()
    }

    /// Returns the current character. This panics if the parser is at EOF.
    fn char(&self) -> Char {
        self.char_at(self.offset())
    }

    /// Peek one character ahead of the current position. If the current
    /// position is the last character, then this returns None.
    fn peek(&self) -> Option<Char> {
        if self.is_eof() {
            return None;
        }
        let next_start = self.offset() + self.char().len();
        utf8::decode(&self.pattern()[next_start..])
    }

    /// Peek two characters ahead of the current position. If the next
    /// position is the last character, then this returns None.
    fn peek2(&self) -> Option<Char> {
        let next = self.peek()?;
        let next2_start = self.offset() + self.char().len() + next.len();
        if next2_start >= self.pattern().len() {
            return None;
        }
        utf8::decode(&self.pattern()[next2_start..])
    }

    /// Peek three characters ahead of the current position. As with peek2, if
    /// there aren't enough positions remaining, then this returns None.
    fn peek3(&self) -> Option<Char> {
        let next = self.peek()?;
        let next2 = self.peek2()?;
        let next3_start =
            self.offset() + self.char().len() + next.len() + next2.len();
        if next3_start >= self.pattern().len() {
            return None;
        }
        utf8::decode(&self.pattern()[next3_start..])
    }

    /// Returns the character at the given byte offset. If the given byte
    /// offset exceeds the length of the pattern, then this panics.
    fn char_at(&self, i: usize) -> Char {
        match utf8::decode(&self.pattern()[i..]) {
            None => panic!("expected char or byte at byte offset {}", i),
            Some(result) => result,
        }
    }

    /// Returns true if and only if all characters in the glob have been
    /// consumed.
    fn is_eof(&self) -> bool {
        self.offset() == self.pattern().len()
    }

    /// Returns the complete raw bytes of the pattern.
    fn pattern(&self) -> &'p [u8] {
        self.pattern
    }

    /// Returns the current byte offset in the pattern that the parser is
    /// currently at. This is always a valid sliceable offset, although it may
    /// point just past the end of the pattern.
    fn offset(&self) -> usize {
        self.offset
    }
}

/// Pushes the given glob into the concatenation of globs while flattening the
/// given glob if necessary.
fn concat_push(concat: &mut Vec<Glob>, glob: Glob) {
    let is_concat = match glob.hir {
        Hir::Concat(_) => true,
        _ => false,
    };
    if is_concat {
        match glob.hir {
            Hir::Concat(globs) => {
                concat.extend(globs);
            }
            _ => unreachable!(),
        }
    } else {
        concat.push(glob);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! syntest {
        ($name:ident, $pattern:expr, $expected:expr) => {
            syntest!($name, $pattern, $expected, Config::default());
        };
        ($name:ident, $pattern:expr, $expected:expr, $config:expr) => {
            #[test]
            fn $name() {
                let mut parser = Parser::new($config);
                let hir = parser.parse(as_bytes($pattern)).unwrap();
                assert_eq!($expected, hir);
            }
        };
    }

    fn as_bytes<'a, B: AsRef<[u8]> + ?Sized>(slice: &'a B) -> &'a [u8] {
        slice.as_ref()
    }

    syntest!(literal1, "a", Glob::codepoint('a'));
    syntest!(literal2, b"\xFF", Glob::byte(b'\xFF'));

    syntest!(anyone1, "?", Glob::any_one_no_separator());
    syntest!(
        anyone2,
        "?",
        Glob::any_one(),
        Config { literal_separator: false, ..Config::default() }
    );
    syntest!(
        anyone3,
        "a?",
        Glob::concat(
            vec![Glob::codepoint('a'), Glob::any_one_no_separator(),]
        )
    );
    syntest!(
        anyone4,
        "?a",
        Glob::concat(vec![Glob::any_one_no_separator(), Glob::codepoint('a')])
    );

    syntest!(anymany1, "*", Glob::any_many_no_separator());
    syntest!(
        anymany2,
        "*",
        Glob::any_many(),
        Config { literal_separator: false, ..Config::default() }
    );
    syntest!(
        anymany3,
        "a*",
        Glob::concat(vec![
            Glob::codepoint('a'),
            Glob::any_many_no_separator(),
        ])
    );
    syntest!(
        anymany4,
        "*a",
        Glob::concat(vec![
            Glob::any_many_no_separator(),
            Glob::codepoint('a')
        ])
    );

    syntest!(sep1, "/", Glob::codepoint('/'));
    syntest!(
        sep2,
        "/",
        Glob::codepoint('/'),
        Config { allow_recursive: false, ..Config::default() }
    );
    syntest!(
        sep3,
        "/a",
        Glob::concat(vec![Glob::codepoint('/'), Glob::codepoint('a')])
    );
    syntest!(
        sep4,
        "/a",
        Glob::concat(vec![Glob::codepoint('/'), Glob::codepoint('a')]),
        Config { allow_recursive: false, ..Config::default() }
    );

    syntest!(rec_after_star1, "**/", Glob::recursive_prefix());
    syntest!(
        win_rec_after_star1,
        r"**\",
        Glob::recursive_prefix(),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        rec_after_star2,
        "**",
        Glob::concat(vec![
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator()
        ])
    );
    syntest!(
        rec_after_star3,
        "a**",
        Glob::concat(vec![
            Glob::codepoint('a'),
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator()
        ])
    );
    syntest!(
        rec_after_star4,
        "**a",
        Glob::concat(vec![
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator(),
            Glob::codepoint('a'),
        ])
    );
    syntest!(
        rec_after_star5,
        "a**b",
        Glob::concat(vec![
            Glob::codepoint('a'),
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator(),
            Glob::codepoint('b'),
        ])
    );

    syntest!(rec_after_sep1, "/**", Glob::recursive_suffix());
    syntest!(
        rec_after_sep2,
        "/**/",
        Glob::concat(vec![Glob::recursive_suffix(), Glob::codepoint('/')])
    );
    syntest!(
        rec_after_sep3,
        "/**a",
        Glob::concat(vec![
            Glob::codepoint('/'),
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator(),
            Glob::codepoint('a'),
        ])
    );

    syntest!(
        win_rec_after_sep1,
        r"\**",
        Glob::recursive_suffix(),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );
    syntest!(
        win_rec_after_sep2,
        r"\**\",
        Glob::concat(vec![Glob::recursive_suffix(), Glob::codepoint('\\')]),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );
    syntest!(
        win_rec_after_sep3,
        r"\**a",
        Glob::concat(vec![
            Glob::codepoint('\\'),
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator(),
            Glob::codepoint('a'),
        ]),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );

    syntest!(
        win_escape_rec_after_sep1,
        r"\\**",
        Glob::recursive_suffix(),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape_rec_after_sep2,
        r"\\**\\",
        Glob::concat(vec![Glob::recursive_suffix(), Glob::codepoint('\\')]),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape_rec_after_sep3,
        r"\\**a",
        Glob::concat(vec![
            Glob::codepoint('\\'),
            Glob::any_many_no_separator(),
            Glob::any_many_no_separator(),
            Glob::codepoint('a'),
        ]),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape_rec_after_sep4,
        r"\\**\\a",
        Glob::concat(vec![
            Glob::recursive_suffix(),
            Glob::codepoint('\\'),
            Glob::codepoint('a')
        ]),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );

    syntest!(
        escape1,
        r"\",
        Glob::codepoint('\\'),
        Config { backslash_escape: true, ..Config::default() }
    );
    syntest!(
        escape2,
        r"\a",
        Glob::codepoint('a'),
        Config { backslash_escape: true, ..Config::default() }
    );
    syntest!(
        escape3,
        r"\*",
        Glob::codepoint('*'),
        Config { backslash_escape: true, ..Config::default() }
    );
    syntest!(
        escape4,
        r"\",
        Glob::codepoint('\\'),
        Config { backslash_escape: false, ..Config::default() }
    );
    syntest!(
        escape5,
        r"\a",
        Glob::concat(vec![Glob::codepoint('\\'), Glob::codepoint('a')]),
        Config { backslash_escape: false, ..Config::default() }
    );
    syntest!(
        escape6,
        r"\*",
        Glob::concat(vec![
            Glob::codepoint('\\'),
            Glob::any_many_no_separator()
        ]),
        Config { backslash_escape: false, ..Config::default() }
    );
    syntest!(
        escape7,
        r"\/**/a",
        Glob::concat(vec![
            Glob::recursive_suffix(),
            Glob::codepoint('/'),
            Glob::codepoint('a')
        ]),
        Config { backslash_escape: true, ..Config::default() }
    );
    syntest!(
        escape8,
        r"\/**\/a",
        Glob::concat(vec![
            Glob::recursive_suffix(),
            Glob::codepoint('/'),
            Glob::codepoint('a')
        ]),
        Config { backslash_escape: true, ..Config::default() }
    );

    syntest!(
        win_escape1,
        r"\",
        Glob::codepoint('\\'),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape2,
        r"\a",
        Glob::codepoint('a'),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape3,
        r"\*",
        Glob::codepoint('*'),
        Config {
            backslash_separator: true,
            backslash_escape: true,
            ..Config::default()
        }
    );
    syntest!(
        win_escape4,
        r"\",
        Glob::codepoint('\\'),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );
    syntest!(
        win_escape5,
        r"\a",
        Glob::concat(vec![Glob::codepoint('\\'), Glob::codepoint('a')]),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );
    syntest!(
        win_escape6,
        r"\*",
        Glob::concat(vec![
            Glob::codepoint('\\'),
            Glob::any_many_no_separator()
        ]),
        Config {
            backslash_separator: true,
            backslash_escape: false,
            ..Config::default()
        }
    );
}
