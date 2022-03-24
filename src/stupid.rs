use std::{io::{BufReader, Read, BufRead}, fs::File, collections::{HashSet, VecDeque}, slice::SliceIndex, rc::Rc};





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


    fn get_next_token(&mut self) -> Option<Token> {

        let has_more = self.refill_current_line();

        let mut token = self.current_line.pop_front();

        match token {

        }

    }
}
