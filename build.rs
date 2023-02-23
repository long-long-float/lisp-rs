use std::process::{Command, Stdio};

fn main() {
    if cfg!(feature = "rv32emu-test") {
        println!("Build rv32emu");
        let output = Command::new("make")
            .args(["-C", "rv32emu"])
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .output()
            .expect("Failed to execute make");
        if !output.status.success() {
            panic!("make failed with status {}", output.status);
        }
    }
}
