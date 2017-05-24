extern crate clap;
extern crate itertools;
extern crate uuid;

use clap::{Arg, App};

use std::fs::File;
use std::io::{self, Write, Read};
use std::path::PathBuf;

mod types;
mod vm;
mod errors;
mod program;
mod time;

use vm::VM;
use errors::MainError;
use program::string::{BinaryProgram, BinaryProgramViewer};

pub type Result<T> = ::std::result::Result<T, MainError>;

fn print_error(e: &MainError) {
    match *e {
        MainError::ParseArgError(ref e) => println!("Could not parse argument: {}", e),
        MainError::FileError(ref e) => println!("Error opening file: {}", e),
        MainError::VMError(ref e) => println!("WVM failed with error: {:?}", e),
    }
}

struct Config {
    memory_size: usize,
    program_path: PathBuf,
}

fn get_args() -> Result<Config> {
    let matches = App::new("Jaime's OCCAM Virtual Machine")
        .version("1.0")
        .author("Jaime Valdemoros <jaime.valdemoros@gmail.com>")
        .about("Corresponding virtual machine for my OCCAM compiler")
        .arg(Arg::with_name("verbose")
                 .long("verbose")
                 .short("v")
                 .multiple(true)
                 .help("verbosity level"))
        .arg(Arg::with_name("memory_size")
                 .long("memory")
                 .short("m")
                 .required(true)
                 .takes_value(true)
                 .help("Size of the memory block available to the program"))
        .arg(Arg::with_name("program")
                 .long("program")
                 .short("p")
                 .required(true)
                 .takes_value(true)
                 .help("Path to the program to run"))
        .get_matches();

    let path: PathBuf = matches
        .value_of("program")
        .unwrap() // Guaranteed by required(true) above
        .into(); // Uses the PathBuf::From<&str> instance
    
    let mem_size: usize = matches
        .value_of("memory_size")
        .unwrap() // Guaranteed by required(true)
        .parse::<usize>()
        .map_err(MainError::ParseArgError)?;

    Ok(Config {
           memory_size: mem_size,
           program_path: path,
       })
}

fn run_main() -> Result<()> {
    let config = get_args()?;

    let program_data: BinaryProgram = {
        let mut buf: Vec<u8> = Vec::new();

        // The File object gets dropped at the end of this
        // scope, closing the file
        File::open(config.program_path)
            .and_then(|mut file| file.read_to_end(&mut buf))
            // We need to explicitly map MainError::FileError
            // before applying the ? operator as we don't want
            // to implement a From instance for IOError into
            // MainError
            .map_err(MainError::FileError)?;

        BinaryProgram::from(buf)
    };

    let mut i = 0;
    for op in &program_data.0 {
        println!("{}: {:?}", i, op); i += 1
    }

    let program = BinaryProgramViewer::from(&program_data);

    let vm = VM::new(config.memory_size, &program)?;

    vm.run().map_err(MainError::from)
}

fn main() {
    if let Err(es) = run_main() {
        print_error(&es)
    }
}
