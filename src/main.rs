mod reader;
mod framestack;
use std::ops::Deref;
use std::cmp::max;
use std::cmp::min;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::File;
use std::io::BufReader;
use std::rc::Rc;

use framestack::FrameStack;

use crate::reader::Label;
use crate::reader::Statement;
use crate::framestack::Assertion;
use crate::reader::{LanguageToken, Tokens, Proof};



// first one is label type,

#[derive(Debug)]
enum LabelEntry {
    DollarA(Assertion),
    DollarP(Assertion),
    DollarE(Statement),
    DollarF(Statement),
}

struct MM {
    fs: FrameStack,
    labels: HashMap<Label, Rc<LabelEntry>>,
    begin_label: Option<String>,
    stop_label: Option<String>,
}

impl MM {
    fn new(begin_label: Option<String>, stop_label: Option<String>) -> MM {
        MM {
            fs: FrameStack::default(),
            labels: HashMap::new(),
            begin_label,
            stop_label,
        }
    }

    fn read(&mut self, toks: &mut Tokens) {
        // println!("Starting function read");
        self.fs.push();
        let mut label: Option<String> = None;
        let mut tok = toks.read_comment();
        // println!("In MM read, found token to be {:?}", tok);
        loop {
            match tok.as_deref() {
                Some("$}") => break,
                Some("$c") => {
                    for tok in toks.readstat().iter() {
                        self.fs.add_c(tok.clone());
                    }
                }
                Some("$v") => {
                    for tok in toks.readstat().iter() {
                        self.fs.add_v(tok.clone());
                    }
                }
                Some("$f") => {
                    let stat = toks.readstat();
                    let label_u: Label = label.expect("$f must have a label").into();
                    if stat.len() != 2 {
                        panic!("$f must have length 2");
                    }

                    // println!("{} $f {} {} $.", label_u, stat[0].clone(), stat[1].clone());
                    self.fs
                        .add_f(stat[1].clone(), stat[0].clone(), label_u.clone());
                    let data = LabelEntry::DollarF(Rc::new([stat[0].clone(), stat[1].clone()]));
                    self.labels.insert(label_u, Rc::new(data));
                    label = None;
                }
                Some("$a") => {
                    let label_u = label.expect("$a must have a label");
                    match &self.stop_label {
                        Some(a) if a == &label_u => std::process::exit(0),
                        _ => {}
                    }

                    let data = LabelEntry::DollarA(self.fs.make_assertion(toks.readstat()));
                    self.labels.insert(label_u.into(), Rc::new(data));
                    label = None;
                }

                Some("$e") => {
                    let label_u: Label = label.expect("e must have label").into();

                    let stat = toks.readstat();
                    self.fs.add_e(stat.clone(), label_u.clone());
                    let data = LabelEntry::DollarE(stat);
                    self.labels.insert(label_u.clone(), Rc::new(data));
                    label = None;
                }
                Some("$p") => {
                    let label_u = label.clone().expect("$p must have elabel");
                    if label == self.stop_label {
                        //could be rewritten better
                        std::process::exit(0);
                    }
                    let stat = toks.readstat();
                    let i = stat
                        .iter()
                        .position(|x| x.as_ref() == "$=")
                        .expect("Mmust have $=");
                    let proof = &stat[i + 1..].to_vec();
                    let stat = &stat[..i];

                    if self.begin_label.is_some() && &label_u == self.begin_label.as_ref().unwrap()
                    {
                        self.begin_label = None;
                    }
                    if self.begin_label.is_none() {
                        println!("verifying {}", label_u);
                        self.verify(label_u.clone(), stat.into(), proof.to_vec());
                    }
                    let data = LabelEntry::DollarP(self.fs.make_assertion(stat.into()));
                    self.labels.insert(label_u.into(), Rc::new(data));
                    label = None;
                }
                Some("$d") => {
                    self.fs.add_d(toks.readstat());
                }
                Some("${") => {
                    self.read(toks);
                }
                Some(x) if !x.starts_with('$') => {
                    label = tok;
                }
                Some(_) => {
                    // print!("tok {:?}", tok);
                }
                None => break,
            }
            tok = toks.read_comment();
        }
        self.fs.list.pop();
    }

    fn apply_subst(
        &self,
        stat: &Statement,
        subst: &HashMap<LanguageToken, Statement>,
    ) -> Statement {
        let mut result: Vec<LanguageToken> = vec![];

        for tok in stat.iter() {
            if subst.contains_key(tok.as_ref()) {
                result.extend(subst[tok.as_ref()].iter().cloned()); //the cloned shouldn't deep copy
            } else {
                result.push(tok.clone());
            }
        }
        result.into()
    }

    fn find_vars(&self, stat: Statement) -> Vec<LanguageToken> {
        let mut vars: Vec<LanguageToken> = vec![];
        for x in stat.iter() {
            if !vars.contains(x) && self.fs.lookup_v(x) {
                vars.push(x.to_owned());
            }
        }

        vars
    }

    fn decompress_and_verify(&mut self, stat: Statement, proof: Proof) {
        // yes I copy pasted this, I know it's bad
        // so please work
         //println!("complete proof {:?}", proof);
         //
        let ep = proof
            .iter()
            .position(|x| x.as_ref() == ")")
            .expect("Failed to find matching parthesis");

        let mut labels: Vec<Rc<str>> = self.get_labels(Rc::clone(&stat), ep);
        let hyp_end = labels.len(); //when the f and e end
        labels.extend((&proof[1..ep]).iter().cloned());

        let compressed_proof = proof[ep + 1..].join("");
        if compressed_proof.is_empty() {
            // we didn't do the proof yet
            return;
        }

        let label_end = labels.len();

         //println!("Labels {:?}", labels);
         //println!("proof {}", compressed_proof);

        // println!("proof_ints: {:?}", proof_ints);

        // println!("labels: {:?}", labels);

        let proof_indeces = Self::get_proof_indeces(compressed_proof);

        type CompressedProof = Rc<[usize]>;
        let mut subproofs: Vec<Statement> = vec![]; //stuff tagged  with Zs
        //let mut prev_proofs: Vec<CompressedProof> = vec![]; // when we contruct a subproof, we have to know the hyps
        let mut stack: Vec<Statement> = vec![];
        let mut previous_proof: Option<Statement> = None;

        for pf_int in &proof_indeces {
            //println!("subproofs : {:?}", subproofs);
            //println!("previous proof : {:?}", previous_proof);
             //println!("pf_int: {:?}, label_end: {:?}", pf_int, label_end);
            match pf_int {
                None => {
                    let last_proof = previous_proof.as_ref().expect("Error in decompressing proof, found unexpected Z");
                    subproofs.push(Rc::clone(last_proof));
                    // println!("Tagging as subproof, subproofs now : {:?}", subproofs.iter().map( |x| x.join(" ") ).collect::<Vec<String>>());

                    // let final_axiom_index = last_proof.last().expect("Error in proof, somehow an empty proof was found");

                    // if *final_axiom_index < label_end {
                    //     // the last one was just a label, just put the statement back
                    //     let label = &labels[*final_axiom_index];
                    //     let data = &self.labels[label];

                    //     match data.as_ref() {
                    //         LabelEntry::DollarA(a) | LabelEntry::DollarP(a) => {

                    //             let Assertion {stat: statement, ..} = a;
                    //             subproofs.push(stat);


                    //         }
                    //         LabelEntry::DollarE(x) | LabelEntry::DollarF(x) => subproofs.push(Rc::clone(x)),
                    //     }

                    // } else {
                    //     //then this means that it was a proof that was already done, so we can just copy that
                    //     subproofs.push(subproofs[*final_axiom_index]);

                    // }
                    // subproofs.push(.clone());
                }
                Some(i) if *i < hyp_end => {
                    //mandatory hypothesis
                    //prev_proofs.push(Rc::new([*i]));
                    let label = &labels[*i];
                    let data = Rc::clone(&self.labels[label]);

                    match data.deref() {
                        LabelEntry::DollarA(a)
                        | LabelEntry::DollarP(a) => {
                            println!("Verifying hypothesis  {:?}", a);
                            let new_prev = self.verify_assertion(&a, &mut stack);
                            previous_proof = Some(new_prev);
                        }
                        LabelEntry::DollarF(x) | LabelEntry::DollarE(x) => {
                            stack.push(x.clone());
                            previous_proof = Some(Rc::clone(x))
                        }
                    }
                }

                Some(i) if hyp_end <= *i && *i < label_end => {
                    //one of the given labels in the proof

                    let label_name = &labels[*i];

                    //println!("Decompressed to label {:?}", label_name);
                    let step_data = Rc::clone(&self.labels[label_name]);

                    match step_data.deref() {
                        LabelEntry::DollarA(a)
                        | LabelEntry::DollarP(a) => {


                            let prev_statement = self.verify_assertion(a, &mut stack);

                            previous_proof = Some(prev_statement);


                            // when we get things that take hypothesis, we have to include those
                            // in the list of previos proof,
                            // let nhyps = shyps.len() + svars.len();

                            // //let new_index = prev_proofs.len() - nhyps;

                            // if nhyps != 0 {
                            //     // first remove all the previous proofs that
                            //     // correpsonded with hypothesis of the axiom/proof
                            //     let mand_hyps: Vec<CompressedProof> =
                            //         prev_proofs.drain(new_index..).collect(); // I tried putting this in oneb ig iterator but it didn't work

                            //     //for the new proof, the new proof consists of
                            //     // first proofs of all the hypothesis
                            //     // once all the hypothesis are satisfied
                            //     // we can apply the axiom/proof
                            //     let new_prevpf = mand_hyps
                            //         .iter()
                            //         .flat_map(|x| x.iter())
                            //         .chain(std::iter::once(i));

                            //     prev_proofs.push(new_prevpf.copied().collect())
                            // } else {
                            //     prev_proofs.push(Rc::new([*i]));
                            // }
                        }
                        LabelEntry::DollarE(x) |  LabelEntry::DollarF(x) => {
                            previous_proof = Some(Rc::clone(x));
                            stack.push(Rc::clone(x));
                        }
                        //_ => prev_proofs.push(Rc::new([*i])),
                    }
                }

                Some(i) if label_end <= *i => {
                    // no need to verify something already proved
                     //println!("alrady proved: *i: {:?}, label_end: {:?}", pf_int, label_end);
                    let pf = &subproofs[(*i as usize) - label_end];
                     //println!("Reusing old proof: {:?}", pf);
                    //prev_proofs.push(pf.clone());
                    //let final_axiom_index = pf.last().expect("Somehow, there was a subproof that proved nothing");
                     //println!("subproofs : {:?}", subproofs);
                    stack.push(Rc::clone(pf));
                    previous_proof = Some(Rc::clone(pf));

                }
                _ => {
                    panic!("Bad compression")
                }
            }
        }

        if stack.len() > 1 {
            panic!("stack has anentry greater than >1 at end")
        }
        if stack[0] != stat {
            panic!("assertion proved {:?} but does not match expected {:?} ", stack[0], stat);
        }

    }

    fn get_labels(&self, stat: Statement, ep: usize) -> Vec<Label> {

        let Assertion {
            dvs: _dm,
            f_hyps: mand_hyp_stmnts,
            e_hyps: hype_stmnts,
            stat: _,
        } = self.fs.make_assertion(stat);
        // println!("mand_hyps_stmnts {:?}", mand_hyp_stmnts);

        let mand_hyps = mand_hyp_stmnts
            .iter()
            .map(|(_k, v)| self.fs.lookup_f(v.clone()));

        let hyps = hype_stmnts.iter().map(|s| self.fs.lookup_e(s.clone()));

        // println!("mand_hyps {:?}", mand_hyps);
        // println!("hyps {:?}", hyps);
        let labels: Vec<Label> = mand_hyps.chain(hyps).collect(); // contains both the mandatory hypotheses and the e println!("Labels {:?}", labels);

        labels
    }

    fn get_proof_indeces(compressed_proof: String) -> Vec<Option<usize>> {
        let mut proof_indeces: Vec<Option<usize>> = vec![];
        let mut cur_index: usize = 0;

        for ch in compressed_proof.chars() {
            if ch == 'Z' {
                proof_indeces.push(None);
            } else if ('A'..='T').contains(&ch) {
                cur_index = 20 * cur_index + (ch as i32 - 'A' as i32 + 1) as usize;
                if cur_index == 0 {
                    panic!("current index was tagged as 0, bad character {}", ch);
                }
                proof_indeces.push(Some(cur_index - 1));
                cur_index = 0;
            } else if ('U'..='Y').contains(&ch) {
                cur_index = 5 * cur_index + (ch as i32 - 'U' as i32 + 1) as usize;
            }
        }
        proof_indeces
    }

    // old version
    fn decompress_proof(&self, stat: Statement, proof: Proof) -> Proof {
        //I should change the type system to differentiate betweene the different types of proofs
        // println!("Statement {:?}", stat);
        //

        let ep = proof
            .iter()
            .position(|x| x.as_ref() == ")")
            .expect("Failed to find matching parthesis");

        let mut labels = self.get_labels(stat, ep);
        let hyp_end = labels.len(); //when the f and e end
        labels.extend((&proof[1..ep]).iter().cloned());

        let compressed_proof = proof[ep + 1..].join("");

        // println!("Labels {:?}", labels);
        // println!("proof {}", compressed_proof);

        // println!("proof_ints: {:?}", proof_ints);

        let label_end = labels.len();
        // println!("labels: {:?}", labels);

        let proof_indeces = Self::get_proof_indeces(compressed_proof);

        let mut decompressed_ints: Vec<usize> = vec![];
        type CompressedProof = Rc<[usize]>;
        let mut subproofs: Vec<CompressedProof> = vec![]; //stuff tagged  with Zs
        let mut prev_proofs: Vec<CompressedProof> = vec![];

        for pf_int in &proof_indeces {
            // println!("subproofs : {:?}", subproofs);
            // println!("pf_int: {:?}, label_end: {:?}", pf_int, label_end);
            match pf_int {
                None => {
                    subproofs.push(
                        prev_proofs
                            .last()
                            .expect("Error in decompressing proof, found unexpected Z")
                            .clone(),
                    );
                }
                Some(i) if *i < hyp_end => {
                    //mandatory hypothesis
                    prev_proofs.push(Rc::new([*i]));
                    decompressed_ints.push(*i);
                }

                Some(i) if hyp_end <= *i && *i < label_end => {
                    //one of the given labels in the proof
                    decompressed_ints.push(*i);

                    let label_name = &labels[*i];

                    let step_data = &self.labels[label_name];

                    match &**step_data {
                        //syntax doesn't look correct
                        LabelEntry::DollarA(Assertion {
                            dvs: _sd,
                            f_hyps: svars,
                            e_hyps: shyps,
                            stat: _sresult,
                        })
                        | LabelEntry::DollarP(Assertion {
                            dvs: _sd,
                            f_hyps: svars,
                            e_hyps: shyps,
                            stat: _sresult,
                        }) => {
                            // when we get things that take hypothesis, we have to include those
                            // in the list of previos proof,
                            let nhyps = shyps.len() + svars.len();

                            let new_index = prev_proofs.len() - nhyps;

                            // let new_prevpf;
                            // if nhyps != 0 {
                            //     let new_index = prev_proofs.len() - nhyps;

                            //     new_prevpf = prev_proofs[(new_index)..]
                            //         .iter()
                            //         .map(|x| x.iter())
                            //         .flatten()
                            //         .chain(std::iter::once(i));
                            //     prev_proofs = prev_proofs[..new_index].to_vec();
                            // } else {
                            //     new_prevpf = std::iter::once(i);
                            // }

                            if nhyps != 0 {
                                let mand_hyps: Vec<CompressedProof> =
                                    prev_proofs.drain(new_index..).collect(); // I tried putting this in oneb ig iterator but it didn't work

                                let new_prevpf = mand_hyps
                                    .iter()
                                    .flat_map(|x| x.iter())
                                    .chain(std::iter::once(i));

                                prev_proofs.push(new_prevpf.copied().collect())
                            } else {
                                prev_proofs.push(Rc::new([*i]));
                            }
                        }
                        _ => prev_proofs.push(Rc::new([*i])),
                    }
                }

                Some(i) if label_end <= *i => {
                    // println!("*i: {:?}, label_end: {:?}", pf_int, label_end);
                    let pf = &subproofs[(*i) - label_end];
                    // println!("expanded subpf {:?}", pf);
                    decompressed_ints.extend(pf.iter());
                    prev_proofs.push(pf.clone());
                }

                _ => {
                    panic!("Bad compression")
                }
            }
        }

        return decompressed_ints
            .iter()
            .map(|i| labels[*i].clone())
            .collect(); //fix the clone
    }
    fn print_stack(stack: &Vec<Statement>) {
                     println!("stack: {:?}", stack.iter().map(|x| x.join(" ")).collect::<Vec<String>>());
}

    fn verify_assertion(&mut self, assertion: &Assertion, stack: &mut Vec<Statement>) -> Statement {

let Assertion {
                    dvs: distinct,
                    f_hyps: mand_var,
                    e_hyps: hyp,
                    stat: result,
                } = assertion;
                    // println!("{:?}", stepdat);
                    //Self::print_stack(stack);
                     //println!("assertion: {:?}", assertion);
                    let npop = mand_var.len() + hyp.len();
                    // println!("stacklength {:?}, ", stack.len());
                    let sp = stack.len() - npop;
                    // println!("npop {:?}, sp {:?}", npop, sp);
                    if stack.len() < npop {
                        panic!("stack underflow")
                    }
                    let mut sp = sp;
                    let mut subst = HashMap::<LanguageToken, Statement>::new();

                    for (k, v) in mand_var {
                        let entry: Statement = stack[sp].clone();
                        // println!("Before checking if equal {:?} : {:?} with sp {:?}", &entry[0], k, sp);

                        if &entry[0] != k {
                            panic!("stack entry doesn't match mandatry var hypothess, found {} and {}", &entry[0], k);
                        }

                        subst.insert(v.clone(), entry[1..].into());
                        sp += 1;
                    }
                    // println!("subst: {:?}", subst);

                    for (x, y) in distinct {
                        // println!("dist {:?} {:?} {:?} {:?}", x, y, subst[x], subst[y]);
                        let x_vars = self.find_vars(Rc::clone(&subst[x]));
                        let y_vars = self.find_vars(subst[y].clone());

                        // println!("V(x) = {:?}", x_vars);
                        // println!("V(y) = {:?}", y_vars);

                        for x in &x_vars {
                            for y in &y_vars {
                                if x == y || !self.fs.lookup_d(x.clone(), y.clone()) {
                                    panic!("Disjoint violation");
                                }
                            }
                        }
                    }
                    for h in hyp {
                        let entry = &stack[sp];
                        let subst_h = self.apply_subst(h, &subst);
                        if entry != &subst_h {
                            panic!("Stack entry: {:?} doesn't match hypothesis {:?}", entry, &subst_h);
                        }
                        sp += 1;
                    }

                    // println!("stack: {:?}", stack);
                    stack.drain(stack.len() - npop..);
                    // println!("stack: {:?}", stack);
                    let substituted = self.apply_subst(result, &subst);
                    stack.push(Rc::clone(&substituted));
                    substituted
                    // println!("stack: {:?}", stack);
    }

    fn verify(&mut self, stat_label: String, stat: Statement, mut proof: Proof) {
        let mut stack: Vec<Statement> = vec![];
        let _stat_type = stat[0].clone();
        if proof[0].as_ref() == "(" {
            // println!("Starting decompression for {}", stat_label);
            // proof = self.decompress_proof(stat.clone(), proof);
            // println!("Finished decompression for {}", stat_label);
            self.decompress_and_verify(stat, proof);
            return;

        }

        if proof.is_empty() {
            println!("Did not find proof for {}, skipping", stat_label);
            return;
        }

        for label in proof {
            let stepdat  = Rc::clone(&self.labels[&label]);
            // println!("{:?} : {:?}", label, self.labels[&label]);

            match stepdat.deref() {
                LabelEntry::DollarA(a)
                | LabelEntry::DollarP(a) => {
                    self.verify_assertion(&a, &mut stack);
                }
                LabelEntry::DollarF(x) | LabelEntry::DollarE(x) => {
                    stack.push(x.clone());
                }
            }
            // // // // println!("st: {:?}", stack);
        }
        if stack.len() != 1 {
            panic!("stack has anentry greater than >1 at end")
        }
        if stack[0] != stat {
            panic!("assertion proved doesn't match ")
        }
    }

    fn dump(&mut self) {
        // println!("{:?}", self.labels);
    }
}
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
