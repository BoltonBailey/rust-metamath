
use nom::{
    branch::alt,
    bytes::complete::{tag, take_till, take_while, take_while1, take_while_m_n},
    character::{
        complete::none_of,
        complete::{multispace0, multispace1},
        is_alphanumeric,
    },
    combinator::{map, map_res},
    error::ParseError,
    multi::{many0, many1},
    sequence::{delimited, tuple},
    IResult,
};

// taken from Appendix E of the metamath language manual
//
//

type MathSymbol = String;
type FileName = String;
type Constant = String;
type Variable = String;
type TypeCode = String;
type Label = String;
type CompressedProofBlock = String;

#[derive(Debug, PartialEq)]
pub struct NonEmptyVec<T>(T, Vec<T>);

impl<T> NonEmptyVec<T> {
    fn new(mut v: Vec<T>) -> NonEmptyVec<T> {
        let drained = v.drain(1..).collect();
        NonEmptyVec(v.remove(0), drained)
    }
}

#[derive(Debug, PartialEq)]
pub struct Database(Vec<OutermostScopeStatement>);

fn database(input: &str) -> IResult<&str, Database> {
    let (input, res) = many0(outermost_scope_stmt)(input)?;
    Ok((input, Database(res)))
}

#[derive(Debug, PartialEq)]
pub enum OutermostScopeStatement {
    IncludeStatement(String),
    ConstantStatement(NonEmptyVec<Constant>), // since it cannot be empty
    Statement(Statement),
}

fn outermost_scope_stmt(input: &str) -> IResult<&str, OutermostScopeStatement> {
    alt((
        include_stmt,
        constant_stmt,
        map(stmt, OutermostScopeStatement::Statement),
    ))(input)
}

fn include_stmt(input: &str) -> IResult<&str, OutermostScopeStatement> {
    let left = delimited(white_space, tag("$c"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let (input, res) = delimited(
        left,
        take_while1(|c| is_printable_character(c) && c != '$' && !c.is_whitespace()),
        right,
    )(input)?;
    Ok((
        input,
        OutermostScopeStatement::IncludeStatement(res.to_string()),
    ))
}

fn constant_stmt(input: &str) -> IResult<&str, OutermostScopeStatement> {
    let left = delimited(white_space, tag("$c"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let (input, res) = delimited(left, many1(math_symbol), right)(input)?;
    Ok((
        input,
        OutermostScopeStatement::ConstantStatement(NonEmptyVec::new(res)),
    ))
}

fn stmt(input: &str) -> IResult<&str, Statement> {
    (alt((
        block,
        variable_stmt,
        disjoint_stmt,
        hypothesis_stmt,
        assert_stmt,
    )))(input)
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    Block(Vec<Statement>),
    VariableStatement(NonEmptyVec<Variable>),
    DisjointStatement(Variable, Variable, Vec<Variable>),
    HypothesisStatement(HypothesisStatement),
    AssertStatement(AssertStatement),
}
fn block(input: &str) -> IResult<&str, Statement> {
    let left = delimited(white_space, tag("${"), white_space);
    let right = delimited(white_space, tag("$}"), white_space);
    let (input, res) = delimited(left, many0(stmt), right)(input)?;
    Ok((input, Statement::Block(res)))
}
fn variable_stmt(input: &str) -> IResult<&str, Statement> {
    let left = delimited(white_space, tag("$v"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let (input, res) = delimited(left, many1(math_symbol), right)(input)?;
    Ok((input, Statement::VariableStatement(NonEmptyVec::new(res))))
}
fn disjoint_stmt(input: &str) -> IResult<&str, Statement> {
    let left = delimited(white_space, tag("$d"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let (input, mut res) = delimited(left, many1(math_symbol), right)(input)?;
    let rest = res.drain(2..).collect();
    let second = res.remove(1);
    let first = res.remove(0);
    Ok((input, Statement::DisjointStatement(first, second, rest)))
}
fn hypothesis_stmt(input: &str) -> IResult<&str, Statement> {
    map(
        alt((floating_stmt, essential_stmt)),
        Statement::HypothesisStatement,
    )(input)
}
fn assert_stmt(input: &str) -> IResult<&str, Statement> {
    map(alt((axiom_stmt, provable_stmt)), Statement::AssertStatement)(input)
}

#[derive(Debug, PartialEq)]
pub enum HypothesisStatement {
    FloatingStatement(Label, TypeCode, Variable),
    EssentialStatement(Label, TypeCode, Vec<MathSymbol>),
}

fn floating_stmt(input: &str) -> IResult<&str, HypothesisStatement> {
    let (input, label_tag) = label(input)?;
    let left = delimited(white_space, tag("$f"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let inside = tuple((math_symbol, math_symbol));
    let (input, (typcode, rest)) = delimited(left, inside, right)(input)?;
    Ok((input, HypothesisStatement::FloatingStatement(label_tag, typcode, rest)))
}
fn essential_stmt(input: &str) -> IResult<&str, HypothesisStatement> {
    let (input, label_tag) = label(input)?;
    let left = delimited(white_space, tag("$e"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let inside = tuple((math_symbol, many0(math_symbol)));
    let (input, (typcode, rest)) = delimited(left, inside, right)(input)?;
    Ok((input, HypothesisStatement::EssentialStatement(label_tag, typcode, rest)))
}

#[derive(Debug, PartialEq)]
pub enum AssertStatement {
    AxiomStatement(Label, TypeCode, Vec<MathSymbol>),
    ProvableStatement(Label, TypeCode, Vec<MathSymbol>, Proof),
}

fn axiom_stmt(input: &str) -> IResult<&str, AssertStatement> {
    let (input, label_tag) = label(input)?;
    let left = delimited(white_space, tag("$a"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let inside = tuple((math_symbol, many0(math_symbol)));
    let (input, (typcode, rest)) = delimited(left, inside, right)(input)?;
    Ok((input, AssertStatement::AxiomStatement(label_tag, typcode, rest)))
}
fn provable_stmt(input: &str) -> IResult<&str, AssertStatement> {
    let (input, label_tag) = label(input)?;
    let (input, _) = delimited(white_space, tag("$p"), white_space)(input)?;
    let (input, type_code) = math_symbol(input)?;
    let (input, statement) = many0(math_symbol)(input)?;
    let (input, _) = delimited(white_space, tag("$="), white_space)(input)?;
    let (input, proof) = proof(input)?;
    let (input, _) = delimited(white_space, tag("$."), white_space)(input)?;
    Ok((input, AssertStatement::ProvableStatement(label_tag, type_code, statement, proof)))
}
#[derive(Debug, PartialEq)]
pub enum Proof {
    UncompressedProof(NonEmptyVec<Option<Label>>), // the option represents whether it is "?"
    CompressedProof(Vec<Label>, NonEmptyVec<CompressedProofBlock>),
}

fn proof(input: &str) -> IResult<&str, Proof> {
    (alt((uncompressed_proof, compressed_proof)))(input)
}
fn uncompressed_proof(input: &str) -> IResult<&str, Proof> {
  todo!()
}
fn compressed_proof(input: &str) -> IResult<&str, Proof> {
  todo!()
}


fn is_printable_character(c: char) -> bool {
    c >= (0x21 as char) && c <= (0x7e as char)
}

fn printable_sequence(input: &str) -> IResult<&str, &str> {
    take_while1(is_printable_character)(input)
}
fn math_symbol(input: &str) -> IResult<&str, MathSymbol> {
    let (input, res) = delimited(
        white_space,
        take_while1(|c| is_printable_character(c) && c != '$'),
        white_space,
    )(input)?;
    Ok((input, res.to_string()))
}

fn label(input: &str) -> IResult<&str, Label> {
    let (input, res) = delimited(
        white_space,
        take_while1(|c: char| c.is_ascii_alphanumeric() || c == '.' || c == '-' || c == '_'),
        white_space,
    )(input)?;
    Ok((input, res.to_string()))
}

fn compressed_proof_block(input: &str) -> IResult<&str, CompressedProofBlock> {
    let (input, res) = delimited(
        white_space,
        take_while1(|c: char| c.is_ascii_uppercase() || c == '?'),
        white_space,
    )(input)?;
    Ok((input, res.to_string()))
}

fn white_space(input: &str) -> IResult<&str, Vec<String>> {
    let (input, res) = many0(comment)(input)?;
    Ok((input, res))
}

fn comment(input: &str) -> IResult<&str, String> {
    let (input, res) = delimited(
        multispace0,
        delimited(tag("$("), many0(none_of("$")), tag("$)")),
        multispace0,
    )(input)?;
    Ok((input, res.iter().collect()))
}

#[cfg(test)]
mod tests {
    use crate::parse::{label, math_symbol};

    #[test]
    fn comment_test1() {
        let (input, res) = math_symbol("$( this is a comment $) abc123 12345").unwrap();

        assert_eq!(res, "abc123");
    }

    #[test]
    fn comment_test2() {
        let (input, res) =
            math_symbol("$( this is a comment $) abc123 12345 $( abcdefgh anthontah n $)").unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test3() {
        let (input, res) = math_symbol(
            "$( this is a comment $) $( anetohuant $) abc123 12345 $( abcdefgh anthontah n $)",
        )
        .unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test4() {
        let (input, res) = label("$( this is a comment $) abc123 12345").unwrap();

        assert_eq!(res, "abc123");
    }

    #[test]
    fn comment_test5() {
        let (input, res) =
            label("$( this is a comment $) abc123 12345 $( abcdefgh anthontah n $)").unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test6() {
        let (input, res) = label(
            "$( this is a comment $) $( anetohuant $) abc123 12345 $( abcdefgh anthontah n $)",
        )
        .unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn bad_label() {
        assert!(label(">>5").is_err());
    }
}
