use nom::{
    branch::alt,
    bytes::complete::{tag, take_while1, take_while, take_until},
    character::{
        complete::none_of,
        complete::{multispace0},
    },
    combinator::{map},
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
pub struct Database(pub Vec<OutermostScopeStatement>);


impl Database {
    pub fn new(input: &str) -> Option<Database> {
        let (input, res) = database(input).ok()?;
        if input == "" {
            Some(res)
        } else {
            None
        }
    }

    pub fn get_vec(self) -> Vec<OutermostScopeStatement> {
        let Database(v) = self;
        v
    }
}

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
    Ok((
        input,
        HypothesisStatement::FloatingStatement(label_tag, typcode, rest),
    ))
}
fn essential_stmt(input: &str) -> IResult<&str, HypothesisStatement> {
    let (input, label_tag) = label(input)?;
    let left = delimited(white_space, tag("$e"), white_space);
    let right = delimited(white_space, tag("$."), white_space);
    let inside = tuple((math_symbol, many0(math_symbol)));
    let (input, (typcode, rest)) = delimited(left, inside, right)(input)?;
    Ok((
        input,
        HypothesisStatement::EssentialStatement(label_tag, typcode, rest),
    ))
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
    Ok((
        input,
        AssertStatement::AxiomStatement(label_tag, typcode, rest),
    ))
}
fn provable_stmt(input: &str) -> IResult<&str, AssertStatement> {
    let (input, label_tag) = label(input)?;
    let (input, _) = delimited(white_space, tag("$p"), white_space)(input)?;
    let (input, type_code) = math_symbol(input)?;
    let (input, statement) = many0(math_symbol)(input)?;
    let (input, _) = delimited(white_space, tag("$="), white_space)(input)?;
    let (input, proof) = proof(input)?;
    let (input, _) = delimited(white_space, tag("$."), white_space)(input)?;
    Ok((
        input,
        AssertStatement::ProvableStatement(label_tag, type_code, statement, proof),
    ))
}
#[derive(Debug, PartialEq)]
pub enum Proof {
    UncompressedProof(NonEmptyVec<Label>),
    CompressedProof(Vec<Label>, NonEmptyVec<CompressedProofBlock>),
}

fn proof(input: &str) -> IResult<&str, Proof> {
    (alt((uncompressed_proof, compressed_proof)))(input)
}
fn uncompressed_proof(input: &str) -> IResult<&str, Proof> {
    let question = map(tag("?"), |x: &str| x.to_string());
    let (input, labels) =
        many0(alt((label, delimited(white_space, question, white_space))))(input)?;
    Ok((input, Proof::UncompressedProof(NonEmptyVec::new(labels))))
}
fn compressed_proof(input: &str) -> IResult<&str, Proof> {
    let (input, _) = delimited(white_space, tag("("), white_space)(input)?;
    let (input, labels) = many0(label)(input)?;
    let (input, _) = delimited(white_space, tag("("), white_space)(input)?;
    let (input, compressed) = many0(compressed_proof_block)(input)?;
    Ok((
        input,
        Proof::CompressedProof(labels, NonEmptyVec::new(compressed)),
    ))
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
    let (input, _) = multispace0(input)?;
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


fn read_no_ws(input: &str) -> IResult<&str, String> {
    let (input, _) = multispace0(input)?;
    let (input, res) = printable_sequence(input)?;
    let (input, _) = multispace0(input)?;
    Ok((input, res.into()))
}


fn read_no_comment(input: &str) -> IResult<&str, String> {
    let (input, token) = read_no_ws(input)?;
    if token.as_str() == "$(" {
        let (input, token) = take_until("$)")(input)?;
        read_no_ws(input)
    } else {
        Ok((input, token))
    }
}



#[cfg(test)]
mod tests {
    use std::fs::read_to_string;

    use nom::{bytes::complete::tag, multi::many1, sequence::delimited};

    use crate::parse::{constant_stmt, database, label, math_symbol, white_space};

    

    #[test]
    fn comment_test1() {
        let (_input, res) = math_symbol("$( this is a comment $) abc123 12345").unwrap();

        assert_eq!(res, "abc123");
    }

    #[test]
    fn comment_test2() {
        let (_input, res) =
            math_symbol("$( this is a comment $) abc123 12345 $( abcdefgh anthontah n $)").unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test3() {
        let (_input, res) = math_symbol(
            "$( this is a comment $) $( anetohuant $) abc123 12345 $( abcdefgh anthontah n $)",
        )
        .unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test4() {
        let (_input, res) = label("$( this is a comment $) abc123 12345").unwrap();

        assert_eq!(res, "abc123");
    }

    #[test]
    fn comment_test5() {
        let (_input, res) =
            label("$( this is a comment $) abc123 12345 $( abcdefgh anthontah n $)").unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn comment_test6() {
        let (_input, res) = label(
            "$( this is a comment $) $( anetohuant $) abc123 12345 $( abcdefgh anthontah n $)",
        )
        .unwrap();

        assert_eq!(res, "abc123");
    }
    #[test]
    fn math_symbol_test1() {
        let (_input, res) = math_symbol("0 abc").unwrap();

        assert_eq!(res, "0");
    }
    #[test]
    fn math_symbol_test2() {
        let (_input, res) = math_symbol("$( 123 abc $) 0 abc").unwrap();

        assert_eq!(res, "0");
    }
    #[test]
    fn math_symbol_test3() {
        let (_input, res) = many1(math_symbol)("$( 123 abc $) 0 abc hi").unwrap();

        assert_eq!(res, vec!["0", "abc", "hi"]);
    }
    #[test]
    fn math_symbol_test4() {
        let parse = many1(math_symbol)("0 0 0");

        println!("{:?}", parse);

        let (_, res) = parse.unwrap();

        assert_eq!(res, vec!["0", "0", "0"]);
    }
    #[test]
    fn math_symbol_test5() {
        let parse = many1(delimited(white_space, tag("0"), white_space))("0 0 0");

        println!("{:?}", parse);

        let (_, res) = parse.unwrap();

        assert_eq!(res, vec!["0", "0", "0"]);
    }
    #[test]
    fn bad_label() {
        assert!(label(">>5").is_err());
    }
    #[test]
    fn metamath_first_proof() {
        let s = r#"$( Declare the constant symbols we will use $)
$c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)
$v t r s P Q $.
$( Specify properties of the metavariables $)
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
$( Define "term" and "wff" $)
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
$( State the axioms $)
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
$( Define the modus ponens inference rule $)
${
min $e |- P $.
maj $e |- ( P -> Q ) $.
mp $a |- Q $.
$}
$( Prove a theorem $)
th1 $p |- t = t $=
$( Here is its proof: $)
tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
tt weq tt tze tpl tt weq tt tt weq wim tt a2
tt tze tpl tt tt a1 mp mp
$."#;
        let parse = database(s);
        println!("{:?}", parse);
        assert!(parse.is_ok());
        assert_eq!(parse.unwrap().0, "");
    }
    #[test]
    fn metamath_first_proof_constant_statement() {
        let s = r#"$( Declare the constant symbols we will use $)
$c 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)"#;
        let parse = constant_stmt(s);
        println!("{:?}", parse);
        assert!(parse.is_ok());
    }
    #[test]
    fn metamath_first_proof_many_math_symbols() {
        let s = r#" 0 + = -> ( ) term wff |- $.
$( Declare the metavariables we will use $)"#;
        let parse = many1(math_symbol)(s);
        println!("{:?}", parse);
        assert!(parse.is_ok());
    }
    #[test]
    fn metamath_first_proof_many_math_symbols_but_less() {
        let s = r#" 0
$( Declare the metavariables we will use $)"#;
        let parse = many1(math_symbol)(s);
        println!("{:?}", parse);
        assert!(parse.is_ok());
    }

    #[test]
    fn parse_setmm_comments() {
        let string = read_to_string("mm/set_comments.mm");


        let string = string.expect("failed to open file");

        let parse = database(&string);

        assert!(parse.is_ok())
    }

}
