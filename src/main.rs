mod database;
mod framestack;
mod reader;
mod stupid;
use std::fs::File;
use std::io::BufReader;

use crate::database::MM;
use crate::reader::Tokens;
use crate::stupid::verify_file;

// first one is label type,

fn main() {
    // println!("Starting proof verification");

    let args: Vec<String> = std::env::args().collect();

    // println!("Got cmd argumnets {:?}", args);
    let file_name = args[1].clone();

    let is_stupid = args.get(2).map(|x| x == "-stupid").is_some();
    if is_stupid {
        verify_file(&file_name);
    } else {
        let mut mm = MM::new(args.get(2).cloned(), args.get(3).cloned());

        let file = File::open(file_name).expect("Failed to find file");

        // println!("Found file name {:?}", args[1]);
        use std::time::Instant;
        let now = Instant::now();

        mm.read(&mut Tokens::new(BufReader::new(file)));
        mm.dump();
        let elapsed = now.elapsed();
        println!("Finished checking in {:.2?}", elapsed);
    }
}
