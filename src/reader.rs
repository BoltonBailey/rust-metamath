use alloc::collections::{BTreeMap, BTreeSet};
use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

// use std::{
//     fs::File,
//     io::{BufRead, BufReader},
// };

#[derive(Debug)]
pub struct Tokens {
    lines_buffer: Vec<String>,
    token_buffer: Vec<String>,
    imported_files: BTreeSet<String>,
}

/// A simple simulator for a file system, keys are filenames, values are file contents
pub struct FileSimulator {
    contents: BTreeMap<String, Vec<String>>,
}

impl FileSimulator {
    pub fn new(map: BTreeMap<String, Vec<String>>) -> FileSimulator {
        FileSimulator { contents: map }
    }
}

//since statement may be used multiple times when applying substitution
// use Rc
pub type Statement = Rc<[LanguageToken]>; //may be better to new type this but I guess it works for now

pub type Proof = Vec<Label>; //I don't think a proof is used multiple times
pub type Label = Rc<str>;
pub type LanguageToken = Rc<str>;

impl Tokens {
    pub fn new(lines: Vec<String>) -> Tokens {
        Tokens {
            lines_buffer: lines,
            token_buffer: vec![],
            imported_files: BTreeSet::new(),
        }
    }
    pub fn read(&mut self) -> Option<String> {
        // println!("inside read function with state {:?}", self);
        while self.token_buffer.is_empty() {
            //println!("Buffer is empty, refilling");
            // let mut line = String::new();
            // pretend this succeeds
            // let result = self.lines_buffer.last_mut().unwrap().read_line(&mut line);
            let result = self.lines_buffer.pop();
            // println!("Read line: {}", line);

            match result {
                Some(line) => {
                    // println!("Read {} lines ", num);
                    self.token_buffer = line.split_whitespace().map(|x| x.into()).collect();
                    self.token_buffer.reverse();
                }
                _ => {
                    // println!("Done with file");
                    self.lines_buffer.pop();
                    if self.lines_buffer.is_empty() {
                        return None;
                    }
                }
            }
            // println!("Created token buffer {:?}", self.token_buffer);
        }
        self.token_buffer.pop()
    }

    fn read_file(&mut self, file_sim: &FileSimulator) -> Option<String> {
        // println!("reading file");

        let mut token = self.read();
        // println!("In read file found token {:?}", token);
        while let Some("$[") = token.as_deref() {
            let filename = self.read().expect("Couldn't find filename");
            let end_bracket = self.read().expect("Couldn't find end bracket");

            // println!("In read file found filename: {:?}, end_bracket: {:?}", filename, end_bracket);
            if end_bracket != "$]" {
                panic!("End bracket not found");
            }

            if !self.imported_files.contains(&filename) {
                // println!("Found new file {}", &filename);

                self.lines_buffer.extend(
                    file_sim
                        .contents
                        .get(&filename)
                        .expect("Should unwrap")
                        .clone(),
                );
                self.imported_files.insert(filename);
            }
            token = self.read();
        }
        token
    }

    pub fn read_comment(&mut self, file_sim: &FileSimulator) -> Option<String> {
        // println!("reading comment");

        loop {
            let mut token = self.read_file(file_sim);
            // println!("In read comment: found token to be {:?}", token);
            match &token {
                None => return None,
                Some(x) if x == "$(" => loop {
                    match token.as_deref() {
                        Some("$)") => break,
                        _ => token = self.read(),
                    }
                },
                _ => return token,
            }
        }
    }

    pub fn read_statement(&mut self, file_sim: &FileSimulator) -> Statement {
        let mut stat: Vec<Rc<str>> = vec![];
        let mut token = self
            .read_comment(file_sim)
            .expect("Failed to read token in read stat");

        // println!("In read stat, found token to be {:?}", token);
        while token != "$." {
            stat.push(token.into());
            token = self.read_comment(file_sim).expect("EOF before $.");
        }
        stat.into()
    }
}
