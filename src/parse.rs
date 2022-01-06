


    use nom::{
  IResult,
  bytes::complete::{tag, take_while_m_n},
  combinator::map_res,
  sequence::tuple};

#[derive(Debug,PartialEq)]
pub struct Color {
  pub red:     u8,
  pub green:   u8,
  pub blue:    u8,
}

//stuff with dollars
#[derive(Debug,PartialEq)]
pub enum Keyword {
    LBrace,
    RBrace,
    C,
    V,
    F,
    E,
    D,
    A,
    P,
    Dot,
    LParen,
    RParen,
    LBracket,
    RBracket,
}

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

pub struct NonEmptyVec<T>(T, Vec<T>);

pub struct Database(Vec<OutermostScopeStatement>);

pub enum OutermostScopeStatement {
    IncludeStatement(String),
    ConstantStatement(NonEmptyVec<Constant>), // since it cannot be empty
    Statement(Statement),
}

pub enum Statement {
    Block(Vec<Statement>),
    VariableStatement(NonEmptyVec<Variable>),
    DisjointStatement(Variable, Variable, Vec<Variable>),
    HypothesisStatement(HypothesisStatement),
    AssertStatement(AssertStatement),
}


pub enum HypothesisStatement {
    FloatingStatement(Label, TypeCode, Variable),
    EssentialStatement(Label, TypeCode, Vec<MathSymbol>),
}


pub enum AssertStatement {
    AxiomStatement(Label, TypeCode, Vec<MathSymbol>),
    ProvableStatement(Label, TypeCode, Vec<MathSymbol>, Proof),
}

pub enum Proof {
    UncompressedProof(NonEmptyVec<Option<Label>>), // the option represents whether it is "?"
    CompressedProof(Vec<Label>, NonEmptyVec<CompressedProofBlock>),
}




fn from_hex(input: &str) -> Result<u8, std::num::ParseIntError> {
  u8::from_str_radix(input, 16)
}


fn dollar_v(input: &str) -> IResult<&str, Keyword> {
    todo!();
}
