#[cfg(feature = "rv32emu-test")]
mod compiler_test {
    use std::env;
    use std::path::Path;
    use std::process::Command;
    use std::str;

    use lisp_rs::lispi::cli_option::CliOption;
    use lisp_rs::lispi::compile;
    use serde_json::Value;

    fn compile_and_run(program: &str) -> Value {
        let program = program.split('\n').map(|l| l.to_string()).collect();

        let dump = env::var("DUMP").is_ok();

        let opt = CliOption {
            filename: None,
            compile: true,
            dump,
            without_opts: false,
        };

        assert!(compile(program, &opt).is_ok());
        assert!(Path::new("out.bin").exists());
        assert!(Path::new("out.elf").exists());

        let output = Command::new("./rv32emu/build/rv32emu")
            .args(["--dump-registers", "-", "--quiet", "out.elf"])
            .output()
            .expect("Failed to execute");

        if dump {
            println!("{}", str::from_utf8(&output.stdout).unwrap_or(""));
        }

        assert!(output.status.success());

        let registers: Value = serde_json::from_slice(&output.stdout).unwrap();
        registers
    }

    #[test]
    fn just_return_42() {
        let registers = compile_and_run("42");
        assert_eq!(Some(42), registers["x10"].as_i64());
    }

    #[test]
    fn add_1_plus_2() {
        let registers = compile_and_run("(+ 1 2)");
        assert_eq!(Some(3), registers["x10"].as_i64());
    }

    #[test]
    fn shift() {
        let registers = compile_and_run("(<< 1 3)");
        assert_eq!(Some(8), registers["x10"].as_i64());

        let registers = compile_and_run("(>> 8 3)");
        assert_eq!(Some(1), registers["x10"].as_i64());

        // TODO: Test about logical/arithmetic shift
    }

    #[test]
    fn variables() {
        let registers = compile_and_run(
            r#"
(define x 10)
(set! x 20)
x
"#,
        );
        assert_eq!(Some(20), registers["x10"].as_i64());
    }

    #[test]
    fn many_variables() {
        let registers = compile_and_run(
            r#"
(define f (lambda (x)
    (define a (+ x x))
    (define b (+ a a))
    (define c (+ b b))
    (define d (+ c c))
    (define e (+ d d))
    (+ e e)
    ))
(f 2)
"#,
        );
        assert_eq!(Some(128), registers["x10"].as_i64());
    }

    #[test]
    fn define_function_and_call() {
        let registers = compile_and_run(
            r#"
(define double (lambda (x) (+ x x)))
(double 21)
"#,
        );
        assert_eq!(Some(42), registers["x10"].as_i64());
    }

    #[test]
    fn define_function_and_call_rank2() {
        let registers = compile_and_run(
            r#"
(define f (lambda (x) (+ x x)))
(define g (lambda (x) (+ (f x) (f x))))
(g 4)
"#,
        );
        assert_eq!(Some(16), registers["x10"].as_i64());
    }

    #[test]
    fn define_function_and_call_directly() {
        let registers = compile_and_run("((lambda (x) (* x x)) 5)");
        assert_eq!(Some(25), registers["x10"].as_i64());
    }

    #[test]
    fn define_recursive_function_and_call() {
        let registers = compile_and_run(
            r#"
(let fact ([x 4]) 
  (if (= x 0)
      1
    (* x (fact (- x 1)))))
"#,
        );
        assert_eq!(Some(24), registers["x10"].as_i64());
    }

    #[test]
    fn load_large_positive_integer() {
        let registers = compile_and_run(
            r#"
2000000000
"#,
        );
        assert_eq!(Some(2000000000), registers["x10"].as_i64());
    }

    #[test]
    fn load_large_negative_integer() {
        let registers = compile_and_run(
            r#"
-2000000000
"#,
        );
        assert_eq!(
            Some(-2000000000),
            registers["x10"].as_i64().map(|i| i as i32)
        );
    }

    #[test]
    fn sum_by_loop() {
        let registers = compile_and_run(
            r#"
(define sum 0)
(let loop ((i 0))
    (set! sum (+ sum i))
    (if (< i 10)
        (loop (+ i 1))))
sum
"#,
        );
        assert_eq!(Some(55), registers["x10"].as_i64());
    }
}
