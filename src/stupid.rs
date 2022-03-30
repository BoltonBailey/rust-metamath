use std::{
    cmp::{max, min},
    collections::{HashMap, HashSet, VecDeque},
    fs::File,
    io::{BufRead, BufReader, Read},
    iter::{self, FromIterator},
    rc::Rc,
};



pub fn verify_file(file_name: &str) {
    let mut verifier = Verifier::new(file_name);
    verifier.read();
    println!("filename was {}", file_name);
}

type Token = Rc<str>; //represents are arbitrary string with no whitespace

struct Reader {
    open_buffers: Vec<BufReader<File>>,
    imported_files: HashSet<String>,
    current_line: VecDeque<Token>,
}

/// almost does the caresian product, but actually only does half of it
/// since the other half is just swapping the left and rgiht
fn self_cartesian_product(variables: Tokens) -> Vec<(Token, Token)> {
    let mut ret = vec![];
    for x in variables.iter() {
        for y in variables.iter() {
            if x != y {
                let min = min(&x, &y);
                let max = max(&x, &y);
                ret.push((Rc::clone(*min), Rc::clone(*max)))
            }
        }
    }

    ret
}

impl Reader {
    fn new(file: &str) -> Self {
        Self {
            open_buffers: vec![BufReader::new(
                File::open(file).expect("File not availabel"),
            )],
            imported_files: HashSet::new(),
            current_line: VecDeque::new(),
        }
    }

    /// return true, means ok
    /// return fales means we are done
    fn refill_current_line(&mut self) -> bool {
        while self.current_line.is_empty() {
            if let Some(current_buffer) = self.open_buffers.last_mut() {
                let mut line = String::new();

                match current_buffer.read_line(&mut line) {
                    Ok(num) if num > 0 => {
                        self.current_line = line.split_whitespace().map(|s| s.into()).collect();
                    }
                    _ => {
                        self.open_buffers.pop();
                    }
                }
            } else {
                return false;
            }
        }
        true
    }

    fn get_next_token_raw(&mut self) -> Option<Token> {
        self.refill_current_line();
        self.current_line.pop_front()
    }

    /// ignores comments and auto importrs files
    fn get_next_token(&mut self) -> Option<Token> {
        let token = self.get_next_token_raw();

        match token {
            Some(x) if x.as_ref() == "$(" => loop {
                match self.get_next_token_raw() {
                    Some(x) if "$)" == x.as_ref() => return self.get_next_token(),
                    _ => {}
                }
            },
            Some(x) if x.as_ref() == "$[" => {
                let filename = self.get_next_token_raw().expect("Couldn't find filename");
                let endbracket = self
                    .get_next_token_raw()
                    .expect("Coludn't find end bracket");

                // println!("In read file found filename: {:?}, endbracket: {:?}", filename, endbracket);
                if endbracket.as_ref() != "$]" {
                    panic!("End bracket not found");
                }

                if !self.imported_files.contains(filename.as_ref()) {
                    // println!("Found new file {}", &filename);
                    self.open_buffers.push(BufReader::new(
                        File::open(filename.as_ref()).expect("Failed to open file"),
                    ));
                    self.imported_files.insert(filename.as_ref().into());
                }
                self.get_next_token()
            }
            x => x,
        }
    }

    fn read_to_period(&mut self) -> Tokens {
        let mut stat: Vec<Rc<str>> = vec![];
        let mut token = self.get_next_token().expect("Failed to read token");
        while token.as_ref() != "$." {
            stat.push(token);
            token = self.get_next_token().expect("EOF before $.");
        }
        stat.into()
    }

    pub fn get_statement(&mut self) -> Option<Statement> {
        let token = self.get_next_token();

        let statement = match token.as_deref() {
            Some("$}") => Statement::ScopeEnd,
            Some("$c") => Statement::Constant(
                self.read_to_period()
                    .iter()
                    .map(|x| Constant(Rc::clone(x)))
                    .collect(),
            ),
            Some("$v") => Statement::Variable(
                self.read_to_period()
                    .iter()
                    .map(|x| Variable(Rc::clone(x)))
                    .collect(),
            ),

            Some("$d") => {
                let variables = self.read_to_period();
                let disjoints = self_cartesian_product(variables)
                    .into_iter()
                    .map(Disjoint)
                    .collect();

                Statement::Disjoint(disjoints)
            }
            Some("${") => Statement::ScopeBegin,
            None => {
                return None;
            }
            Some(label) => match self.get_next_token().as_deref() {
                Some("$f") => match &self.read_to_period()[..] {
                    [label, sort, token] => Statement::Floating(Floating {
                        label: Rc::clone(label),
                        sort: Rc::clone(sort),
                        token: Rc::clone(token),
                    }),
                    _ => panic!("Incorrect syntax for floating"),
                },
                Some("$a") => {
                    let sort = self.get_next_token().expect("Could not find first token");
                    let statement = self.read_to_period();

                    Statement::Axiom(Axiom {
                        statement,
                        sort,
                        label: label.into(),
                    })
                }
                Some("$e") => {
                    let sort = self
                        .get_next_token()
                        .expect("Could not find first variable for ");
                    let statement = self.read_to_period();

                    Statement::Essential(Essential {
                        statement,
                        sort,
                        label: label.into(),
                    })
                }
                Some("$p") => {
                    let sort = self
                        .get_next_token()
                        .expect("Could not find first variable for ");
                    let statement_and_proof = self.read_to_period();
                    let split: Vec<_> = statement_and_proof.split(|x| x.as_ref() == "$=").collect();

                    match &split[..] {
                        [statement, proof] => Statement::Proof(Proof {
                            statement: Rc::from(*statement),
                            sort,
                            label: label.into(),
                            proof: Rc::from(*proof),
                        }),
                        _ => panic!("Too many $="),
                    }
                }
                _ => {
                    panic!("Error after reading label {}", label)
                }
            },
        };
        Some(statement)
    }
}

pub struct FrameStack {
    frames: Vec<Frame>,
}

impl FrameStack {
    fn add_statement(&mut self, statement: &Statement) {
        match statement {
            Statement::ScopeEnd => {
                self.frames.pop();
            }
            Statement::Constant(constants) => {
                let frame = self.frames.last_mut().expect("Failed to find frame");
                for token in constants {
                    let Constant(token) = token;
                    if frame.constants.contains(&Constant(Rc::clone(token))) {
                        panic!(
                            "Tried to add {} as constant, but was already declared as a Constant",
                            token
                        )
                    }
                    if frame.variables.contains(&Variable(Rc::clone(token))) {
                        panic!(
                            "Tried to add {} as constant, but was already declared as a variable",
                            token
                        )
                    }
                    frame.constants.insert(Constant(Rc::clone(token)));
                }
            }
            Statement::Variable(variable) => {
                let frame = self.frames.last_mut().expect("Failed to find frame");
                for token in variable {
                    let Variable(token) = token;
                    if frame.constants.contains(&Constant(Rc::clone(token))) {
                        panic!(
                            "Tried to add {} as variable, but was already declared as a constant",
                            token
                        )
                    }
                    if frame.variables.contains(&Variable(Rc::clone(token))) {
                        panic!(
                            "Tried to add {} as variable, but was already declared as a variable",
                            token
                        )
                    }
                    frame.variables.insert(Variable(Rc::clone(token)));
                }
            }
            Statement::Floating(floating) => {
                //let Floating { sort, token, label } = floating;

                let sort = Rc::clone(&floating.sort);
                let token = Rc::clone(&floating.token);

                if !self.lookup_variable(&token) {
                    panic!("{} was not defined as a variable", token)
                }
                if !self.lookup_constant(&token) {
                    panic!("{} was not defined as a constant", sort)
                }

                let frame = self.frames.last_mut().expect("Failed to find frame");
                frame.floating.push(floating.clone());
            }
            Statement::Axiom(_axiom) => {}
            Statement::Essential(essential) => {
                let frame = self.frames.last_mut().expect("Failed to find frame");
                frame.essential.push(essential.clone());
            }
            Statement::Proof(_) => todo!(),
            Statement::Disjoint(disjoints) => {
                let frame = self.frames.last_mut().expect("Failed to find frame");
                let disjoint_set: HashSet<Disjoint> = HashSet::from_iter(disjoints.iter().cloned());
                frame.disjoint.extend(disjoint_set);
            }
            Statement::ScopeBegin => todo!(),
        };
    }

    fn lookup_constant(&self, constant: &Token) -> bool {
        self.frames
            .iter()
            .rev()
            .any(|fr| fr.constants.contains(&Constant(Rc::clone(constant))))
    }

    fn lookup_variable(&self, variable: &Token) -> bool {
        self.frames
            .iter()
            .rev()
            .any(|fr| fr.variables.contains(&Variable(Rc::clone(variable))))
    }

    fn lookup_floating(&self, variable: &Token) -> Label {
        let _frame = self
            .frames
            .iter()
            .rev()
            .find(|frame| {
                frame
                    .floating
                    .iter()
                    .any(|floating| &floating.token == variable)
            })
            .expect("Could not find floating token");

        todo!()
    }
    fn lookup_d(&self, _x: Token, _y: Token) -> bool {
        todo!()
    }
    fn lookup_e(&self, _stmt: Statement) -> Label {
        todo!()
    }

    fn make_assertion(&self, statement: Tokens) -> Assertion {
        let essential: Vec<_> = self
            .frames
            .iter()
            .flat_map(|frame| frame.essential.iter())
            .cloned()
            .collect();
        let essential_statements: Vec<_> = self
            .frames
            .iter()
            .flat_map(|frame| frame.essential.iter().map(|e| Rc::clone(&e.statement)))
            .collect();

        let chained = essential_statements.iter().chain(iter::once(&statement));

        let mandatory: Tokens = chained
            .flat_map(|statement| statement.iter())
            .filter(|token| self.lookup_variable(token))
            .cloned()
            .collect();

        let cartesian: HashSet<_> = self_cartesian_product(Rc::clone(&mandatory))
            .into_iter()
            .map(Disjoint)
            .collect();

        let disjoint: HashSet<Disjoint> = self
            .frames
            .iter()
            .flat_map(|frame| frame.disjoint.intersection(&cartesian))
            .cloned()
            .collect();

        let mut floating: VecDeque<Floating> = VecDeque::new();
        let mut mandatory: HashSet<_> = mandatory.iter().collect();
        self.frames.iter().rev().for_each(|fr| {
            fr.floating.iter().rev().for_each(|float| {
                if mandatory.contains(&float.token) {
                    floating.push_front(float.clone());
                    mandatory.remove(&float.token);
                }
            });
        });
        Assertion {
            disjoint,
            floating,
            essential,
            statement,
        }
    }

    fn convert_to_statement(&self, tokens: Tokens) -> Proposition {
        tokens
            .iter()
            .map(|token| {
                if self.lookup_constant(token) {
                    Term::Constant(Constant(Rc::clone(token)))
                } else if self.lookup_variable(token) {
                    Term::Variable(Variable(Rc::clone(token)))
                } else {
                    panic!("token {} not declared as constant or variable", token);
                }
            })
            .collect()
    }

    fn new() -> FrameStack {
        FrameStack {
            frames: vec![Frame::new()],
        }
    }
}

impl Default for FrameStack {
    fn default() -> Self {
        Self::new()
    }
}

// not exactyl suer if this is the right terminloogy.
type Proposition = Vec<Term>;

enum Term {
    Variable(Variable),
    Constant(Constant),
}

struct Assertion {
    disjoint: HashSet<Disjoint>,
    floating: VecDeque<Floating>,
    essential: Vec<Essential>,
    statement: Tokens,
}

enum LabelEntry {
    Floating(Floating),
    Essential(Essential),
    Axiom(Axiom),
    Proof(Proof),
}
pub struct Verifier {
    framestack: FrameStack,
    reader: Reader,
    labels: HashMap<Label, LabelEntry>,
}

impl Verifier {
    fn read(&mut self) {
        loop {
            let statement = self.reader.get_statement();

            match statement {
                Some(statement) => {
                    self.framestack.add_statement(&statement);
                    match statement {
                        Statement::Floating(f) => {
                            self.labels
                                .insert(Rc::clone(&f.label), LabelEntry::Floating(f));
                        }
                        Statement::Axiom(a) => {
                            self.labels
                                .insert(Rc::clone(&a.label), LabelEntry::Axiom(a));
                        }
                        Statement::Essential(e) => {
                            self.labels
                                .insert(Rc::clone(&e.label), LabelEntry::Essential(e));
                        }
                        Statement::Proof(p) => {
                            self.labels
                                .insert(Rc::clone(&p.label), LabelEntry::Proof(p));
                            //p.verify();
                        }
                        _ => {}
                    }
                }
                None => break,
            }
        }
    }

    pub(crate) fn new(file_path: &str) -> Verifier {
        Verifier {
            framestack: FrameStack::new(),
            reader: Reader::new(file_path),
            labels: HashMap::new(),
        }
    }
}

type Tokens = Rc<[Token]>;
type MathStatement = Tokens;
type Label = Token;

#[derive(Eq, Hash, PartialEq)]
struct Constant(Token);

#[derive(Eq, Hash, PartialEq)]
struct Variable(Token);
#[derive(Eq, Hash, PartialEq, Clone)]
struct Disjoint((Token, Token));

#[derive(Eq, Hash, PartialEq, Clone)]
struct Floating {
    sort: Token,
    token: Token,
    label: Label,
}
#[derive(Eq, Hash, PartialEq, Clone)]
struct Essential {
    statement: MathStatement,
    sort: Token,
    label: Label,
}
#[derive(Eq, Hash, PartialEq, Clone)]
struct Axiom {
    statement: MathStatement,
    sort: Token,
    label: Label,
}
#[derive(Eq, Hash, PartialEq, Clone)]
struct Proof {
    statement: MathStatement,
    sort: Token,
    proof: Tokens,
    label: Label,
}

/// THins to parse inot
enum Statement {
    ScopeEnd,
    Constant(Vec<Constant>),
    Variable(Vec<Variable>),
    Floating(Floating),
    Axiom(Axiom),
    Essential(Essential),
    Proof(Proof),
    Disjoint(Vec<Disjoint>),
    ScopeBegin,
}

pub struct Frame {
    constants: HashSet<Constant>,
    variables: HashSet<Variable>,
    floating: Vec<Floating>,
    essential: Vec<Essential>,
    disjoint: HashSet<Disjoint>,
}

impl Frame {
    pub fn new() -> Self {
        Self {
            constants: HashSet::new(),
            variables: HashSet::new(),
            floating: Vec::new(),
            essential: Vec::new(),
            disjoint: HashSet::new(),
        }
    }
}
impl Proof {
    fn verify(&self) {
        todo!()
    }
}
