use std::{
    fs::File,
    io::{self, BufRead},
    path::Path,
};

use super::error::Error;

pub fn read_lines<P>(filename: P) -> Result<Vec<String>, Error>
where
    P: AsRef<Path>,
{
    if let Ok(file) = File::open(filename) {
        let lines = io::BufReader::new(file)
            .lines()
            .filter_map(|line| line.ok())
            .collect::<Vec<String>>();
        Ok(lines)
    } else {
        Err(Error::Io("Cannot open source file".to_string()))
    }
}
