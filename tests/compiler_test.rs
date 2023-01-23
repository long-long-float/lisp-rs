use std::path::Path;
use std::process::Command;

use lisp_rs::lispi::compile;
use serde_json::Value;

#[test]
#[cfg(feature = "rv32emu-test")]
fn basic_compiler_test() {
    assert_eq!(true, compile(vec!["42".to_string()]).is_ok());
    assert_eq!(true, Path::new("out.bin").exists());
    assert_eq!(true, Path::new("out.elf").exists());

    let output = Command::new("./rv32emu/build/rv32emu")
        .args(["--dump-registers", "out.elf"])
        .output()
        .expect(&format!("Failed to execute"));

    assert_eq!(true, output.status.success());

    let registers: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(Some(0), registers["x0"].as_i64());
    assert_eq!(Some(40), registers["x1"].as_i64());
    // TODO: Check all registers
}
