#[cfg(feature = "rv32emu-test")]
mod compiler_test {
    use colored::Colorize;
    use core::time;
    use itertools::Itertools;
    use serde_json::Value;
    use std::collections::HashSet;
    use std::fs::{create_dir, File};
    use std::io::Write;
    use std::path::Path;
    use std::process::{Command, Output, Stdio};
    use std::str;
    use std::{env, thread};

    use function_name::named;
    use lisp_rs::lispi;
    use lisp_rs::lispi::cli_option::CliOption;
    use lisp_rs::lispi::opt;

    /// Timeout for execution the emulator in seconds
    const TIMEOUT_EMU: u32 = 5;

    struct Compiler {
        name: &'static str,
        program: &'static str,
        optimizations: HashSet<opt::Optimize>,
    }

    impl Compiler {
        fn min_opts(self) -> Self {
            Self {
                optimizations: opt::Optimize::minimum(),
                ..self
            }
        }

        fn run(self) -> Value {
            let output = self.internal_run(true);
            serde_json::from_slice(&output.stdout).unwrap()
        }

        fn run_raw_output(self) -> String {
            let output = self.internal_run(false);
            let output = String::from_utf8(output.stdout)
                .unwrap()
                .chars()
                .rev()
                .skip_while(|c| c == &'\0')
                .join("");
            output.chars().rev().join("")
        }

        fn internal_run(self, dump_registers: bool) -> Output {
            let Self {
                name,
                program,
                optimizations,
            } = self;

            if !name.is_empty() {
                let dir_name = Path::new("compiler_test_files");
                if !dir_name.exists() {
                    create_dir(dir_name).expect("Cannot create test dir");
                }
                let mut file = File::create(dir_name.join(format!("{}.scm", name))).unwrap();
                file.write_all(program.as_bytes()).unwrap();
            }

            let program = program.split('\n').map(|l| l.to_string()).collect();

            let dump = env::var("DUMP").is_ok();

            let opt = CliOption {
                filename: None,
                compile: true,
                dump,
                without_opts: false,
            };

            assert!(lispi::compile(program, &opt, optimizations).is_ok());
            assert!(Path::new("out.bin").exists());
            assert!(Path::new("out.elf").exists());

            let mut args = vec!["--quiet"];
            if dump_registers {
                args.append(&mut vec!["--dump-registers", "-"]);
            }
            args.push("out.elf");

            let mut child = Command::new("./rv32emu/build/rv32emu")
                .args(args)
                .stdout(Stdio::piped())
                .spawn()
                .expect("Failed to spawn rv32emu.");

            let mut over_timeout = true;
            for _ in 0..(TIMEOUT_EMU * 10) {
                match child.try_wait() {
                    Ok(Some(status)) => {
                        assert!(status.success());

                        over_timeout = false;
                        break;
                    }
                    Ok(None) => {}
                    Err(e) => panic!("error attempting to wait: {e}"),
                }

                thread::sleep(time::Duration::from_millis(100));
            }

            if over_timeout {
                child.kill().expect("Failed to kill rv32emu.");
                panic!("{}", "Timeout during execution on rv32emu.".yellow());
            }

            let output = child.wait_with_output().unwrap();

            if dump {
                println!("{}", str::from_utf8(&output.stdout).unwrap_or(""));
            }

            output
        }
    }

    fn compile(name: &'static str, program: &'static str) -> Compiler {
        Compiler {
            name,
            program,
            optimizations: opt::Optimize::all(),
        }
    }

    trait ValueExtension {
        fn as_i32(&self) -> Option<i32>;
    }

    impl ValueExtension for Value {
        fn as_i32(&self) -> Option<i32> {
            self.as_i64().map(|v| v as i32)
        }
    }

    #[test]
    #[named]
    fn just_return_42() {
        let registers = compile(function_name!(), "42").run();
        assert_eq!(Some(42), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn arith_add() {
        let registers = compile(function_name!(), "(+ 1 2)").min_opts().run();
        assert_eq!(Some(3), registers["x10"].as_i32());

        let registers = compile(function_name!(), "(+ 1 -2)").min_opts().run();
        assert_eq!(Some(-1), registers["x10"].as_i32());
    }

    #[test]
    #[named]
    fn arith_sub() {
        let registers = compile(function_name!(), "(- 1 2)").min_opts().run();
        assert_eq!(Some(-1), registers["x10"].as_i32());

        let registers = compile(function_name!(), "(- 1 -2)").min_opts().run();
        assert_eq!(Some(3), registers["x10"].as_i32());
    }

    #[test]
    #[named]
    fn arith_mul() {
        let registers = compile(function_name!(), "(* 2 3)").min_opts().run();
        assert_eq!(Some(6), registers["x10"].as_i32());

        let registers = compile(function_name!(), "(* 2 -3)").min_opts().run();
        assert_eq!(Some(-6), registers["x10"].as_i32());
    }

    #[test]
    #[named]
    fn arith_div() {
        let registers = compile(function_name!(), "(/ 6 3)").min_opts().run();
        assert_eq!(Some(2), registers["x10"].as_i32());

        let registers = compile(function_name!(), "(/ 5 3)").min_opts().run();
        assert_eq!(Some(1), registers["x10"].as_i32());

        let registers = compile(function_name!(), "(/ 6 -3)").min_opts().run();
        assert_eq!(Some(-2), registers["x10"].as_i32());
    }

    #[test]
    fn shift() {
        let registers = compile("", "(<< 1 3)").min_opts().run();
        assert_eq!(Some(8), registers["x10"].as_i64());

        let registers = compile("", "(>> 8 3)").min_opts().run();
        assert_eq!(Some(1), registers["x10"].as_i64());

        // TODO: Test about logical/arithmetic shift
    }

    #[test]
    #[named]
    fn write_string() {
        let output = compile(function_name!(), r#"(write "Hello\n")"#).run_raw_output();
        assert_eq!("Hello\n", output);
    }

    #[test]
    #[named]
    fn variables() {
        let registers = compile(
            function_name!(),
            r#"
(define x 10)
(set! x 20)
x
"#,
        )
        .run();
        assert_eq!(Some(20), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn function_many_variables() {
        let registers = compile(
            function_name!(),
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
        )
        .run();
        assert_eq!(Some(128), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn function_simple_call() {
        let registers = compile(
            function_name!(),
            r#"
(define double (lambda (x) (+ x x)))
(double 21)
"#,
        )
        .run();
        assert_eq!(Some(42), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn function_call_rank2() {
        let registers = compile(
            function_name!(),
            r#"
(define f (lambda (x) (+ x x)))
(define g (lambda (x) (+ (f x) (f x))))
(g 4)
"#,
        )
        .run();
        assert_eq!(Some(16), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn function_pass_lambda() {
        let registers = compile(
            function_name!(),
            r#"
(define call (lambda (fun x) (fun x)))
(call (lambda (x) (+ x x)) 21)
"#,
        )
        .run();
        assert_eq!(Some(42), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn function_call_directly() {
        let registers = compile(function_name!(), "((lambda (x) (+ x x)) 5)").run();
        assert_eq!(Some(10), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn let_recursive_function() {
        let registers = compile(
            function_name!(),
            r#"
(let sum ([x 10]) 
  (if (< x 1)
      0
    (+ x (sum (- x 1)))))
"#,
        )
        .run();
        assert_eq!(Some(55), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn let_let_add() {
        let registers = compile(
            function_name!(),
            r#"
(let* ([x 2] [y 3]) (+ x y))
"#,
        )
        .run();
        assert_eq!(Some(5), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn load_large_positive_integer() {
        let registers = compile(
            function_name!(),
            r#"
2000000000
"#,
        )
        .run();
        assert_eq!(Some(2000000000), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn load_large_negative_integer() {
        let registers = compile(
            function_name!(),
            r#"
-2000000000
"#,
        )
        .run();
        assert_eq!(
            Some(-2000000000),
            registers["x10"].as_i64().map(|i| i as i32)
        );
    }

    #[test]
    #[named]
    fn tail_recursion_sum_by_loop() {
        let registers = compile(
            function_name!(),
            r#"
(define sum 0)
(let loop ((i 0))
    (set! sum (+ sum i))
    (if (< i 10)
        (loop (+ i 1))))
sum
"#,
        )
        .run();
        assert_eq!(Some(55), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_len() {
        let registers = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->len ary)
"#,
        )
        .run();
        assert_eq!(Some(3), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_in_function() {
        let registers = compile(
            function_name!(),
            r#"
(define f (lambda () 
    (define ary (array 1 2 3))
    (array->get ary 1)))
(define g (lambda () (f)))
(g)
"#,
        )
        .run();
        assert_eq!(Some(2), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_get_1() {
        let registers = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->get ary 1)
"#,
        )
        .run();
        assert_eq!(Some(2), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_get_by_variable() {
        let registers = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (array 1 2 3))
    (array->get ary i)
    ))
(f 1)
"#,
        )
        .run();
        assert_eq!(Some(2), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_set_by_variable() {
        let registers = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (array 1 2 3))
    (array->set ary i 99)
    (array->get ary i)
    ))
(f 1)
"#,
        )
        .run();
        assert_eq!(Some(99), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_set_1() {
        let registers = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->set ary 1 99)
(array->get ary 1)
"#,
        )
        .run();
        assert_eq!(Some(99), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_get_1_char() {
        let registers = compile(
            function_name!(),
            r#"
(define ary "01234")
(array->get ary 1)
"#,
        )
        .run();
        assert_eq!(Some('1' as i64), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn array_set_1_char() {
        let registers = compile(
            function_name!(),
            r#"
(define ary "01234")
(array->set ary 1 \X)
(array->get ary 1)
"#,
        )
        .run();
        assert_eq!(Some('X' as i64), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn as_char_to_int() {
        let registers = compile(function_name!(), "(as #\\0 int)").run();
        assert_eq!(Some('0' as i64), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn struct_get_1st_field() {
        let registers = compile(
            function_name!(),
            r#"
(struct Point
    [x int]
    [y int])
(define pos (Point 10 20))
(Point->x pos)
"#,
        )
        .run();
        assert_eq!(Some(10), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn struct_get_2nd_field() {
        let registers = compile(
            function_name!(),
            r#"
(struct Point
    [x int]
    [y int])
(define pos (Point 10 20))
(Point->y pos)
"#,
        )
        .run();
        assert_eq!(Some(20), registers["x10"].as_i64());
    }

    #[test]
    #[named]
    fn struct_get_3rd_field_mixed_types() {
        let registers = compile(
            function_name!(),
            r#"
(struct ABC
    [a char]
    [b int]
    [c char])
(define abc (ABC \a 0xb \c))
(ABC->c abc)
"#,
        )
        .run();
        assert_eq!(Some('c' as i64), registers["x10"].as_i64());
    }
}
