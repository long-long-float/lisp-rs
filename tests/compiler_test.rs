use std::path::Path;
use std::process::Command;

use lisp_rs::lispi::compile;
use serde_json::Value;

fn compile_and_run(program: &str) -> Value {
    let program = program.split('\n').map(|l| l.to_string()).collect();

    assert_eq!(true, compile(program, false).is_ok());
    assert_eq!(true, Path::new("out.bin").exists());
    assert_eq!(true, Path::new("out.elf").exists());

    let output = Command::new("./rv32emu/build/rv32emu")
        .args(["--dump-registers", "out.elf"])
        .output()
        .expect(&format!("Failed to execute"));

    assert_eq!(true, output.status.success());

    let registers: Value = serde_json::from_slice(&output.stdout).unwrap();
    println!("{:#?}", registers);
    registers
}

#[test]
#[cfg(feature = "rv32emu-test")]
fn just_return_42() {
    let registers = compile_and_run("42");
    assert_eq!(Some(42), registers["x10"].as_i64());
}

#[test]
#[cfg(feature = "rv32emu-test")]
fn add_1_plus_2() {
    let registers = compile_and_run("(+ 1 2)");
    assert_eq!(Some(3), registers["x10"].as_i64());
}

#[test]
#[cfg(feature = "rv32emu-test")]
fn function1() {
    let registers = compile_and_run(
        r#"
(define double (lambda (x) (+ x x)))
(double 21)
"#,
    );
    assert_eq!(Some(42), registers["x10"].as_i64());
}
