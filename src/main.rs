mod framestack;
mod reader;
mod database;
use std::fs::File;
use std::io::BufReader;

use crate::database::MM;
use crate::reader::Tokens;

// first one is label type,

fn main() {
    // println!("Starting proof verification");

    let args: Vec<String> = std::env::args().collect();

    // println!("Got cmd argumnets {:?}", args);

    let mut mm = MM::new(args.get(2).cloned(), args.get(3).cloned());

    let file = File::open(args[1].clone()).expect("Failed to find file");
    // println!("Found file name {:?}", args[1]);
    use std::time::Instant;
    let now = Instant::now();

    mm.read(&mut Tokens::new(BufReader::new(file)));
    mm.dump();
    let elapsed = now.elapsed();
    println!("Finished checking in {:.2?}", elapsed);
}
