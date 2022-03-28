use std::{io::{BufReader, Read, BufRead}, fs::File, collections::{HashSet, VecDeque, HashMap}, slice::SliceIndex, rc::Rc};





pub fn verify_file(file_name: &str) {
    println!("filename was {}", file_name);
}


type Token = Rc<str>; //represents are arbitrary string with no whitespace

struct Reader {
    open_buffers: Vec<BufReader<File>>,
    imported_files: HashSet<String>,
    current_line: VecDeque<Token>
}

impl Reader {

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

        let mut token = self.get_next_token_raw();

        match token {
            Some(x) if x.as_ref() == "$(" => loop {
                match self.get_next_token_raw() {
                    Some(x) if "$)" == x.as_ref() => return self.get_next_token(),
                    _ => {},
                }
            }
            Some(x) if x.as_ref() == "$[" => {
                let filename = self.get_next_token_raw().expect("Couldn't find filename");
                let endbracket = self.get_next_token_raw().expect("Coludn't find end bracket");

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
                return self.get_next_token();
            }
            x => return x,
        }
    }

    fn read_statement(&self) -> Statement {
        todo!()
    }
}
type Tokens = Rc<[Token]>;
type MathStatement = Tokens;
type Label = Token;
struct Constant(Token);
struct Variable(Token);
struct Disjoint((Token, Token));
struct Floating {
    sort: Token,
    token: Token,
    label: Label,
}
struct Essential {
    statement: MathStatement,
    sort: Token,
    label: Label,
}
struct Axiom {
    statement: MathStatement,
    sort: Token,
    label: Label,
}
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
