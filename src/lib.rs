///! Adapted from https://bodil.lol/parser-combinators/
use combinators::*;
use parsers::*;
pub type ParseResult<'a, Output> = Result<(&'a str, Output), &'a str>;

/// Shared trait among all combinators
pub(crate) trait Parser<'a, Output> {
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output>;
}

impl<'a, F, Output> Parser<'a, Output> for F
where
    F: Fn(&'a str) -> ParseResult<'a, Output>,
{
    fn parse(&self, input: &'a str) -> ParseResult<'a, Output> {
        self(input)
    }
}

pub(crate) mod parsers {
    use super::*;
    /// Creates a parser that matches the passed in literal
    ///
    /// ### Example
    /// ```ignore
    /// let parse_joe = match_literal("Hello Joe!");
    /// assert_eq!(Ok(("", ())), parse_joe.parse("Hello Joe!"));
    /// assert_eq!(
    ///     Ok((" Hello Robert!", ())),
    ///     parse_joe.parse("Hello Joe! Hello Robert!")
    /// );
    /// assert_eq!(Err("Hello Mike!"), parse_joe.parse("Hello Mike!"));
    /// ```
    pub(crate) fn match_literal<'a>(expected: &'static str) -> impl Parser<'a, ()> {
        move |input: &'a str| match input.get(0..expected.len()) {
            Some(next) if next == expected => Ok((&input[expected.len()..], ())),
            _ => Err(input),
        }
    }

    pub(crate) fn front_matter(input: &str) -> ParseResult<String> {
        let mut matched = String::new();
        let chars = input.chars();
        let mut dash_count = 0;
        let mut plus_count = 0;

        for next in chars {
            if next == '\n' && (dash_count == 3 || plus_count == 3) {
                matched.pop();
                matched.pop();
                matched.pop();
                break;
            }
            match next {
                '-' => {
                    dash_count += 1;
                    matched.push(next);
                }
                '+' => {
                    plus_count += 1;
                    matched.push(next);
                }
                _ => {
                    dash_count = 0;
                    plus_count = 0;
                    matched.push(next);
                }
            }
        }

        let next_index = matched.len();
        Ok((&input[next_index..], matched))
    }
}

mod combinators {
    use super::*;
    /// Creates and sets up the second parser to run immediately after the first
    pub(crate) fn pair<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, (R1, R2)>
    where
        P1: Parser<'a, R1>,
        P2: Parser<'a, R2>,
    {
        move |input| {
            parser1.parse(input).and_then(|(next_input, result1)| {
                parser2
                    .parse(next_input)
                    .map(|(last_input, result2)| (last_input, (result1, result2)))
            })
        }
    }

    pub(crate) fn or<'a, P1, P2, R>(parser1: P1, parser2: P2) -> impl Parser<'a, R>
    where
        P1: Parser<'a, R>,
        P2: Parser<'a, R>,
    {
        move |input| match parser1.parse(input) {
            Ok(val) => Ok(val),
            Err(input) => parser2.parse(input),
        }
    }

    pub(crate) fn map<'a, P, F, A, B>(parser: P, map_fn: F) -> impl Parser<'a, B>
    where
        P: Parser<'a, A>,
        F: Fn(A) -> B,
    {
        move |input| {
            parser
                .parse(input)
                .map(|(next_input, result)| (next_input, map_fn(result)))
        }
    }

    pub(crate) fn left<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R1>
    where
        P1: Parser<'a, R1>,
        P2: Parser<'a, R2>,
    {
        map(pair(parser1, parser2), |(left, _right)| left)
    }

    pub(crate) fn right<'a, P1, P2, R1, R2>(parser1: P1, parser2: P2) -> impl Parser<'a, R2>
    where
        P1: Parser<'a, R1>,
        P2: Parser<'a, R2>,
    {
        map(pair(parser1, parser2), |(_left, right)| right)
    }

    pub(crate) fn one_or_more<'a, P, A>(parser: P) -> impl Parser<'a, Vec<A>>
    where
        P: Parser<'a, A>,
    {
        move |mut input| {
            let mut result = Vec::new();

            if let Ok((next_input, first_item)) = parser.parse(input) {
                input = next_input;
                result.push(first_item);
            } else {
                return Err(input);
            }

            while let Ok((next_input, next_item)) = parser.parse(input) {
                input = next_input;
                result.push(next_item)
            }

            Ok((input, result))
        }
    }

    pub(crate) fn any_char(input: &str) -> ParseResult<char> {
        match input.chars().next() {
            Some(next) => Ok((&input[next.len_utf8()..], next)),
            _ => Err(input),
        }
    }

    pub(crate) fn pred<'a, P, A, F>(parser: P, predicate: F) -> impl Parser<'a, A>
    where
        P: Parser<'a, A>,
        F: Fn(&A) -> bool,
    {
        move |input| {
            if let Ok((next_input, value)) = parser.parse(input) {
                if predicate(&value) {
                    return Ok((next_input, value));
                }
            }
            Err(input)
        }
    }

    pub(crate) fn whitespace_char<'a>() -> impl Parser<'a, char> {
        pred(any_char, |c| c.is_whitespace())
    }
}

pub fn matter(input: &str) -> Option<(String, String)> {
    match split_matter(input) {
        Ok((front, content)) => Some((front, content)),
        Err(val) => {
            dbg!(val);
            None
        }
    }
}

pub fn split_matter(input: &str) -> Result<(String, String), &str> {
    let delimiter = or(match_literal("---"), match_literal("+++"));
    let delimiter_2 = or(match_literal("---"), match_literal("+++"));
    let parser = right(
        right(delimiter, one_or_more(whitespace_char())),
        left(
            front_matter,
            pair(delimiter_2, one_or_more(whitespace_char())),
        ),
    );
    parser
        .parse(input)
        .map(|(content, front)| (front, content.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn literal_parser() {
        let parse_joe = match_literal("Hello Joe!");
        assert_eq!(Ok(("", ())), parse_joe.parse("Hello Joe!"));
        assert_eq!(
            Ok((" Hello Robert!", ())),
            parse_joe.parse("Hello Joe! Hello Robert!")
        );
        assert_eq!(Err("Hello Mike!"), parse_joe.parse("Hello Mike!"));
    }

    #[test]
    fn one_or_more_combinator() {
        let parser = one_or_more(match_literal("ha"));
        assert_eq!(Ok(("", vec![(), (), ()])), parser.parse("hahaha"));
        assert_eq!(Err("ahah"), parser.parse("ahah"));
        assert_eq!(Err(""), parser.parse(""));
    }

    #[test]
    fn predicate_combinator() {
        let parser = pred(any_char, |c| *c == 'o');
        assert_eq!(Ok(("mg", 'o')), parser.parse("omg"));
        assert_eq!(Err("lol"), parser.parse("lol"));
    }

    #[test]
    fn or_combinator() {
        let tag_opener = or(match_literal("<"), match_literal(">"));
        assert_eq!(Ok(("", ())), tag_opener.parse("<"));
        assert_eq!(Ok(("", ())), tag_opener.parse(">"));
        assert_eq!(Ok(("Jeremy", ())), tag_opener.parse(">Jeremy"));
    }

    #[test]
    fn split_matter_combinator() {
        let sample = r#"---
name: Dustin
---
# Hello world!"#;
        let (front, content) = split_matter(sample).unwrap();
        assert_eq!(String::from("name: Dustin\n"), front);
        assert_eq!(String::from("# Hello world!"), content);
    }
}

#[cfg(test)]
mod matter_tests {
    use super::split_matter;

    #[test]
    fn extract_toml() {
        let contents = r#"+++
title = "TOML Frontmatter"
list = [
    "Of",
    "Things",
]
[[assets]]
contentType = "audio/mpeg"
+++

This is some content."#;

        let (f, c) = split_matter(contents).unwrap();
        assert_ne!(f.len(), 0);
        assert_eq!(c, "This is some content.");
    }

    #[test]
    fn extract_basic_yaml() {
        let contents = r#"---
title: YAML Frontmatter
---

This is some content."#;

        let (f, c) = split_matter(contents).unwrap();

        assert_eq!(f, "title: YAML Frontmatter\n");
        assert_eq!(c, "This is some content.");
    }

    #[test]
    fn extract_unquoted_yaml() {
        let contents = r#"---
title: Yaml Frontmatter --- Revenge of the Unquoted Strings
---

This is some content."#;

        let (f, c) = split_matter(contents).unwrap();

        assert_eq!(
            f,
            "title: Yaml Frontmatter --- Revenge of the Unquoted Strings\n"
        );
        assert_eq!(c, "This is some content.");
    }

    #[test]
    fn extract_multiline_yaml() {
        let contents = r#"---
text: |
    Nested multiline content, which may---contain loosely-formatted text.
---

This is some content."#;

        let (f, c) = split_matter(contents).unwrap();

        let substr = r#"text: |
    Nested multiline content, which may---contain loosely-formatted text.
"#;
        assert_eq!(f, substr);
        assert_eq!(c, "This is some content.");
    }

    #[test]
    fn extract_nested_yaml() {
        let contents = r#"---
availability: public
when:
  start: 1471/3/28 MTR 4::22
  duration: 0::30
date: 2012-02-18
title: Rutejìmo
---

Text"#;

        let (f, c) = split_matter(contents).unwrap();

        assert_ne!(f.len(), 0);
        assert_eq!(c, "Text");
    }
}
