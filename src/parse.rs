


    use nom::{
  IResult,
  bytes::complete::{tag, take_while_m_n},
  combinator::map_res,
  sequence::tuple};


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

#[derive(Debug,PartialEq)]
pub struct NonEmptyVec<T>(T, Vec<T>);

#[derive(Debug,PartialEq)]
pub struct Database(Vec<OutermostScopeStatement>);

#[derive(Debug,PartialEq)]
pub enum OutermostScopeStatement {
    IncludeStatement(String),
    ConstantStatement(NonEmptyVec<Constant>), // since it cannot be empty
    Statement(Statement),
}

#[derive(Debug,PartialEq)]
pub enum Statement {
    Block(Vec<Statement>),
    VariableStatement(NonEmptyVec<Variable>),
    DisjointStatement(Variable, Variable, Vec<Variable>),
    HypothesisStatement(HypothesisStatement),
    AssertStatement(AssertStatement),
}


#[derive(Debug,PartialEq)]
pub enum HypothesisStatement {
    FloatingStatement(Label, TypeCode, Variable),
    EssentialStatement(Label, TypeCode, Vec<MathSymbol>),
}


#[derive(Debug,PartialEq)]
pub enum AssertStatement {
    AxiomStatement(Label, TypeCode, Vec<MathSymbol>),
    ProvableStatement(Label, TypeCode, Vec<MathSymbol>, Proof),
}

#[derive(Debug,PartialEq)]
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
