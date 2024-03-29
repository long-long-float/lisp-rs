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
    use lisp_rs::lispi::cli_option::{CliOption, DumpOptions};
    use lisp_rs::lispi::pass;

    /// Timeout for execution the emulator in seconds
    const TIMEOUT_EMU: u32 = 5;

    struct Compiler<'a> {
        name: &'static str,
        program: &'a str,
        optimizations: HashSet<pass::Optimize>,
    }

    impl<'a> Compiler<'a> {
        fn min_opts(self) -> Self {
            Self {
                optimizations: pass::Optimize::minimum(),
                ..self
            }
        }

        fn run(self) -> Value {
            let output = self.internal_run(true);
            serde_json::from_slice(&output.stdout).unwrap()
        }

        fn run_a0(self) -> Option<i64> {
            let output = self.run();
            output["int_regs"]
                .as_array()
                .and_then(|regs| regs[10].as_object())
                .and_then(|reg| reg["value"].as_i64())
        }

        /// Useful for negative values
        fn run_a0_i32(self) -> Option<i32> {
            self.run_a0().map(|v| v as i32)
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
                compile: true,
                dump: if dump {
                    vec![DumpOptions::All]
                } else {
                    Vec::new()
                },
                ..Default::default()
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

    fn compile<'a>(name: &'static str, program: &'a str) -> Compiler<'a> {
        Compiler {
            name,
            program,
            optimizations: pass::Optimize::all(),
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
        let a0 = compile(function_name!(), "42").run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn arith_add() {
        let a0 = compile(function_name!(), "(+ 1 2)").min_opts().run_a0_i32();
        assert_eq!(Some(3), a0);

        let a0 = compile(function_name!(), "(+ 1 -2)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(-1), a0);
    }

    #[test]
    #[named]
    fn arith_sub() {
        let a0 = compile(function_name!(), "(- 1 2)").min_opts().run_a0_i32();
        assert_eq!(Some(-1), a0);

        let a0 = compile(function_name!(), "(- 1 -2)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(3), a0);
    }

    #[test]
    #[named]
    fn arith_mul() {
        let a0 = compile(function_name!(), "(* 2 3)").min_opts().run_a0_i32();
        assert_eq!(Some(6), a0);

        let a0 = compile(function_name!(), "(* 2 -3)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(-6), a0);
    }

    #[test]
    #[named]
    fn arith_div() {
        let a0 = compile(function_name!(), "(/ 6 3)").min_opts().run_a0_i32();
        assert_eq!(Some(2), a0);

        let a0 = compile(function_name!(), "(/ 5 3)").min_opts().run_a0_i32();
        assert_eq!(Some(1), a0);

        let a0 = compile(function_name!(), "(/ 6 -3)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(-2), a0);
    }

    #[test]
    #[named]
    fn arith_mod() {
        let a0 = compile(function_name!(), "(% 13 10)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(3), a0);

        let a0 = compile(function_name!(), "(% 6 3)").min_opts().run_a0_i32();
        assert_eq!(Some(0), a0);

        let a0 = compile(function_name!(), "(% -13 10)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(-3), a0);

        let a0 = compile(function_name!(), "(% 13 -10)")
            .min_opts()
            .run_a0_i32();
        assert_eq!(Some(3), a0);
    }

    #[test]
    fn arith_cmp_less_than() {
        assert_eq!(Some(1), compile("", "(< 1 2)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(< 2 1)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(< -1 -2)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(< -2 -1)").min_opts().run_a0());
    }

    #[test]
    fn arith_cmp_less_than_and_eq() {
        assert_eq!(Some(1), compile("", "(<= 1 2)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(<= 2 1)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(<= 2 2)").min_opts().run_a0());
    }

    #[test]
    fn arith_cmp_greater_than() {
        assert_eq!(Some(0), compile("", "(> 1 2)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(> 2 1)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(> -1 -2)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(> -2 -1)").min_opts().run_a0());
    }

    #[test]
    fn arith_cmp_greater_than_and_eq() {
        assert_eq!(Some(0), compile("", "(>= 1 2)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(>= 2 1)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(>= 2 2)").min_opts().run_a0());
    }

    #[test]
    fn shift() {
        let a0 = compile("", "(<< 1 3)").min_opts().run_a0();
        assert_eq!(Some(8), a0);

        let a0 = compile("", "(>> 8 3)").min_opts().run_a0();
        assert_eq!(Some(1), a0);

        // TODO: Test about logical/arithmetic shift
    }

    #[test]
    fn logical_op_and() {
        assert_eq!(Some(0), compile("", "(and #f #f)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(and #t #f)").min_opts().run_a0());
        assert_eq!(Some(0), compile("", "(and #f #t)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(and #t #t)").min_opts().run_a0());
    }

    #[test]
    fn logical_op_or() {
        assert_eq!(Some(0), compile("", "(or #f #f)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(or #t #f)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(or #f #t)").min_opts().run_a0());
        assert_eq!(Some(1), compile("", "(or #t #t)").min_opts().run_a0());
    }

    #[test]
    #[named]
    fn write_string_3times() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(println "Hello")
(println "Hello")
(println "Hello")
"#,
        )
        .run_raw_output();
        assert_eq!("Hello\nHello\nHello\n", output);
    }

    #[test]
    #[named]
    fn variables() {
        let a0 = compile(
            function_name!(),
            r#"
(define x 10)
(set! x 20)
x
"#,
        )
        .run_a0();
        assert_eq!(Some(20), a0);
    }

    #[test]
    #[named]
    fn function_many_variables() {
        let a0 = compile(
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
        .run_a0();
        assert_eq!(Some(128), a0);
    }

    #[test]
    #[named]
    fn function_simple_call() {
        let a0 = compile(
            function_name!(),
            r#"
(define double (lambda (x) (+ x x)))
(double 21)
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn function_call_rank2() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (x) (+ x x)))
(define g (lambda (x) (+ (f x) (f x))))
(g 4)
"#,
        )
        .run_a0();
        assert_eq!(Some(16), a0);
    }

    #[test]
    #[named]
    fn function_pass_lambda() {
        let a0 = compile(
            function_name!(),
            r#"
(define call (lambda (fun x) (fun x)))
(call (lambda (x) (+ x x)) 21)
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn function_call_directly() {
        let a0 = compile(function_name!(), "((lambda (x) (+ x x)) 5)").run_a0();
        assert_eq!(Some(10), a0);
    }

    #[test]
    #[named]
    fn let_recursive_function() {
        let a0 = compile(
            function_name!(),
            r#"
(let sum ((x 10)) 
  (if (< x 1)
      0
    (+ x (sum (- x 1)))))
"#,
        )
        .run_a0();
        assert_eq!(Some(55), a0);
    }

    #[test]
    #[named]
    fn let_let_add() {
        let a0 = compile(
            function_name!(),
            r#"
(let* ((x 2) (y 3)) (+ x y))
"#,
        )
        .run_a0();
        assert_eq!(Some(5), a0);
    }

    #[test]
    #[named]
    fn load_large_positive_integer() {
        let a0 = compile(
            function_name!(),
            r#"
2000000000
"#,
        )
        .run_a0();
        assert_eq!(Some(2000000000), a0);
    }

    #[test]
    #[named]
    fn load_large_negative_integer() {
        let a0 = compile(
            function_name!(),
            r#"
-2000000000
"#,
        )
        .run_a0();
        assert_eq!(Some(-2000000000), a0.map(|i| i as i32));
    }

    #[test]
    #[named]
    fn tail_recursion_sum_by_loop() {
        let a0 = compile(
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
        .run_a0();
        assert_eq!(Some(55), a0);
    }

    #[test]
    #[named]
    fn cond_eq_char() {
        fn run_cond(input: char) -> Option<i64> {
            let program = format!(
                r#"
(define op #\{input})
(cond
    ((= op #\+) 1)
    ((= op #\-) 2)
    (#t 0))
"#
            );

            compile(function_name!(), &program).run_a0()
        }

        assert_eq!(Some(1), run_cond('+'));
        assert_eq!(Some(2), run_cond('-'));
        assert_eq!(Some(0), run_cond('*'));
    }

    #[test]
    #[named]
    fn array_len() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->len &ary)
"#,
        )
        .run_a0();
        assert_eq!(Some(3), a0);
    }

    #[test]
    #[named]
    fn array_in_function() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda () 
    (define ary (array 1 2 3))
    (array->get &ary 1)))
(define g (lambda () (f)))
(g)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn array_get_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->get &ary 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn array_get_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (array 1 2 3))
    (array->get &ary i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn array_set_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (array 1 2 3))
    (array->set &ary i 99)
    (array->get &ary i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(99), a0);
    }

    #[test]
    #[named]
    fn array_set_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (array 1 2 3))
(array->set &ary 1 99)
(array->get &ary 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(99), a0);
    }

    #[test]
    #[named]
    fn fixed_array_len() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (fixed-array 1 2 3))
(array->len &ary)
"#,
        )
        .run_a0();
        assert_eq!(Some(3), a0);
    }

    #[test]
    #[named]
    fn fixed_array_in_function() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda () 
    (define ary (fixed-array 1 2 3))
    (array->get &ary 1)))
(define g (lambda () (f)))
(g)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn fixed_array_get_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (fixed-array 1 2 3))
(array->get &ary 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn fixed_array_get_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (fixed-array 1 2 3))
    (array->get &ary i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn fixed_array_set_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define ary (fixed-array 1 2 3))
    (array->set &ary i 99)
    (array->get &ary i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(99), a0);
    }

    #[test]
    #[named]
    fn fixed_array_set_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary (fixed-array 1 2 3))
(array->set &ary 1 99)
(array->get &ary 1)
"#,
        )
        .run_a0();
        assert_eq!(Some(99), a0);
    }

    #[test]
    #[named]
    fn fixed_array_get_1_from_returned_array() {
        let a0 = compile(
            function_name!(),
            r#"
(fn make-fixed-array ()
    (define ary (fixed-array 10 11 12 13 14))
    ary)

(define ary (make-fixed-array))
(array->get &ary 1) 
"#,
        )
        .run_a0();
        assert_eq!(Some(11), a0);
    }

    #[test]
    #[named]
    fn fixed_array_set_1_to_returned_array() {
        let a0 = compile(
            function_name!(),
            r#"
(fn make-fixed-array ()
    (define ary (fixed-array 10 11 12 13 14))
    ary)

(define ary (make-fixed-array))
(array->set &ary 1 42) 
(array->get &ary 1) 
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn string_len() {
        let a0 = compile(
            function_name!(),
            r#"
(define str "Hello")
(array->len &str)
"#,
        )
        .run_a0();
        assert_eq!(Some(5), a0);
    }

    #[test]
    #[named]
    fn string_in_function() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda () 
    (define str "Hello")
    (array->get &str 1)))
(define g (lambda () (f)))
(g)
"#,
        )
        .run_a0();
        assert_eq!(Some('e' as i64), a0);
    }

    #[test]
    #[named]
    fn string_get_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define str "Hello")
(array->get &str 1)
"#,
        )
        .run_a0();
        assert_eq!(Some('e' as i64), a0);
    }

    #[test]
    #[named]
    fn string_get_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define str "Hello")
    (array->get &str i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some('e' as i64), a0);
    }

    #[test]
    #[named]
    fn string_set_by_variable() {
        let a0 = compile(
            function_name!(),
            r#"
(define f (lambda (i)
    (define str "Hello")
    (array->set &str i \x)
    (array->get &str i)
    ))
(f 1)
"#,
        )
        .run_a0();
        assert_eq!(Some('x' as i64), a0);
    }

    #[test]
    #[named]
    fn string_set_1() {
        let a0 = compile(
            function_name!(),
            r#"
(define str "Hello")
(array->set &str 1 \x)
(array->get &str 1)
"#,
        )
        .run_a0();
        assert_eq!(Some('x' as i64), a0);
    }

    #[test]
    #[named]
    fn as_char_to_int() {
        let a0 = compile(function_name!(), "(as #\\0 int)").run_a0();
        assert_eq!(Some('0' as i64), a0);
    }

    #[test]
    #[named]
    fn struct_get_1st_field() {
        let a0 = compile(
            function_name!(),
            r#"
(struct Point
    x: int
    y: int)
(define pos (Point 10 20))
(Point->x &pos)
"#,
        )
        .run_a0();
        assert_eq!(Some(10), a0);
    }

    #[test]
    #[named]
    fn struct_get_2nd_field() {
        let a0 = compile(
            function_name!(),
            r#"
(struct Point
    x: int
    y: int)
(define pos (Point 10 20))
(Point->y &pos)
"#,
        )
        .run_a0();
        assert_eq!(Some(20), a0);
    }

    #[test]
    #[named]
    fn struct_set_2nd_field() {
        let a0 = compile(
            function_name!(),
            r#"
(struct Point
    x: int
    y: int)
(define pos (Point 10 20))
(Point->y= &pos 42)
(Point->y &pos)
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn struct_get_3rd_field_mixed_types() {
        let a0 = compile(
            function_name!(),
            r"
(struct ABC
    a: char
    b: int
    c: char)
(define abc (ABC \a 0xb \c))
(ABC->c &abc)
",
        )
        .run_a0();
        assert_eq!(Some('c' as i64), a0);
    }

    #[test]
    #[named]
    fn struct_pass_reference_of_struct() {
        let a0 = compile(
            function_name!(),
            r"
(struct Person
    id: int
    age: int)

(fn Person->inc_age (self)
    (define age (Person->age self))
    (Person->age= self (+ age 1)))

(define person (Person 0 18))
(Person->inc_age &person)
(Person->age &person)
",
        )
        .run_a0();
        assert_eq!(Some(19), a0);
    }

    #[test]
    #[named]
    fn reference_ref() {
        let a0 = compile(
            function_name!(),
            r#"
(define x 10)
(ref x)
"#,
        )
        .run_a0();
        // Don't check the value due to random address.
        assert!(a0.is_some());
    }

    #[test]
    #[named]
    fn reference_ref_shorthand() {
        // Shorthand notation
        let a0 = compile(
            function_name!(),
            r#"
(define x 10)
(= &x (ref x))
"#,
        )
        .run_a0();
        assert_eq!(Some(1), a0);
    }

    #[test]
    #[named]
    fn reference_deref() {
        let a0 = compile(
            function_name!(),
            r#"
(define x 10)
(define x-ptr (ref x))
(deref x-ptr)
"#,
        )
        .run_a0();
        assert_eq!(Some(10), a0);
    }

    #[test]
    #[named]
    fn reference_ref_set() {
        let a0 = compile(
            function_name!(),
            r#"
(define x 10)
(define x-ptr (ref x))
(ref-set x-ptr 42)
(deref x-ptr)
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn reference_result_of_accessor() {
        let a0 = compile(
            function_name!(),
            r#"
(struct Struct
    inner: fixed-array[int 5])

(define s (Struct (fixed-array 0 0 0 0 0)))
(array->set &(Struct->inner &s) 2 42)
(array->get &(Struct->inner &s) 2)
"#,
        )
        .run_a0();
        assert_eq!(Some(42), a0);
    }

    #[test]
    #[named]
    fn reference_array_ref() {
        let a0 = compile(
            function_name!(),
            r#"
(define ary &"123")
(if (< 0 (array->len ary))
    (array->get ary 0)
    #\0)
"#,
        )
        .run_a0();
        assert_eq!(Some('1' as i64), a0);
    }

    #[test]
    #[named]
    fn reference_array_ref_through_fun() {
        let a0 = compile(
            function_name!(),
            r#"
(fn first-or (ary default)
    (if (< 0 (array->len ary))
        (array->get ary 0)
        default))
(first-or &"123" #\0)
"#,
        )
        .run_a0();
        assert_eq!(Some('1' as i64), a0);
    }

    #[test]
    #[named]
    fn complex_program_array_sum() {
        let a0 = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(fn array->sum (ary)
    (define sum 0)
    (define len (- (array->len &ary) 1))
    (let loop ((i 0)) 
        (set! sum (+ sum (array->get &ary i)))
        (if (< i len)
            (loop (+ i 1))))
    sum)

(define ary (array 1 2 3))
(array->sum ary)
"#,
        )
        .run_a0();
        assert_eq!(Some(6), a0);
    }

    #[test]
    #[named]
    fn complex_program_nested_for() {
        let a0 = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(define sum 0)
(for (i 0) (< i 5) (+ i 1) (begin
    (for (j 0) (< j 5) (+ j 1) (begin
        (for (k 0) (< k 5) (+ k 1) (begin
            (set! sum (+ sum 1))
        ))  
    ))   
))
sum
"#,
        )
        .run_a0();
        assert_eq!(Some(125), a0);
    }

    #[test]
    #[ignore] // This causes stack overflow and needs `RUST_MIN_STACK=104857600`.
    #[named]
    fn complex_program_count_digit() {
        let a0 = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(struct Context
    cursor: int)

(fn is_digit (ch) (begin
    (define chi (as ch int))
    (and (<= (as #\0 int) chi) (<= chi (as #\9 int)))))

(fn count-digit (ctx input)
    (define digit 0)
    (for (i (Context->cursor ctx)) 
        (and (is_digit (array->get input i)) (< i (array->len input))) 
        (+ i 1)
        (begin
            (println-int digit)
            (set! digit (+ digit 1))))
    digit)

(count-digit &(Context 0) &"123")
"#,
        )
        .run_a0();
        assert_eq!(Some(123), a0);
    }

    #[test]
    #[named]
    fn complex_program_returning_32bits_struct() {
        let a0 = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(struct Context
    cursor: int)

(fn count-digit (ctx input)
    (define digit 0)
    (for (i (Context->cursor ctx))
        (and (= (array->get input i) #\0) (< i 2)) 
        (+ i 1)
        (set! digit (+ digit 1)))
    digit)

(fn count-digit2 (ctx input)
    (count-digit ctx input))

(count-digit2 &(Context 0) &"00")
"#,
        )
        .run_a0();
        assert_eq!(Some(2), a0);
    }

    #[test]
    #[named]
    fn complex_program_string_to_int() {
        let a0 = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(fn string->int (str)
    (define sum 0)
    (define len (- (array->len &str) 1))
    (define digit 1)
    (let loop ((i len)) 
        (define n (char->int (array->get &str i)))
        (set! sum (+ sum (* n digit)))
        (set! digit (* digit 10))
        (if (< 0 i)
            (loop (- i 1))))
    sum)
(string->int "123")
"#,
        )
        .run_a0();
        assert_eq!(Some(123), a0);
    }

    #[test]
    #[named]
    fn complex_program_for() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(for (i 0) (< i 3) (+ i 1) (begin
    (println "Hello")))
"#,
        )
        .run_raw_output();
        assert_eq!("Hello\nHello\nHello\n", output);
    }

    #[test]
    #[ignore] // This causes stack overflow and needs `RUST_MIN_STACK=104857600`.
    #[named]
    fn complex_program_println_int() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(fn println-int2 (value)
    (define digit 1)
    (for (i 1) (< 0 (/ value i)) (* i 10)
        (set! digit i))
    (set! digit (/ digit 10))
    (for (d digit) (< 0 d) (/ d 10) (begin
        (print-char (int->char (/ value d)))
        (set! value (% value d))
        ))
    (println ""))
(println-int2 1995)
"#,
        )
        .run_raw_output();
        assert_eq!("1995\n", output);
    }

    #[test]
    #[named]
    fn complex_program_for_2times() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(for (i 0) (< i 3) (+ i 1) (begin
    (println "Hello")))
(for (i 0) (< i 3) (+ i 1) (begin
    (println "Hello")))
"#,
        )
        .run_raw_output();
        assert_eq!("Hello\nHello\nHello\nHello\nHello\nHello\n", output);
    }

    #[test]
    #[ignore] // This causes stack overflow and needs `RUST_MIN_STACK=104857600`.
    #[named]
    fn complex_program_calc_v1() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(struct Context
    cursor: int)

(fn is_digit (ch)
    (define chi (as ch int))
    (and (<= (as #\0 int) chi) (<= chi (as #\9 int))))

(fn count-digit (ctx input)
    (define digit 0)
    (for (i (Context->cursor ctx)) 
        (and (is_digit (array->get input i)) (< i (array->len input))) 
        (+ i 1)
        (set! digit (+ digit 1)))
    digit)

(fn parse-int (ctx input)
    (define sum 0)
    (define len (count-digit ctx input))
    (define digit 1)
    (define start (Context->cursor ctx))
    (for (i (- len 1)) (>= i 0) (- i 1) (begin
        (define n (char->int (array->get input (+ start i))))
        (set! sum (+ sum (* n digit)))
        (set! digit (* digit 10))))
    (Context->cursor= ctx (+ start len))
    sum)
    
(fn parse-op (ctx input)
    (define op (array->get input (Context->cursor ctx)))
    (Context->cursor= ctx (+ (Context->cursor ctx) 1))
    op)

(fn calc-expr (ctx input)
    (define left (parse-int ctx input))
    (define op (parse-op ctx input))
    (define right (parse-int ctx input))
    (+ left right))

(fn calc (input)
    (define ctx (Context 0))
    (calc-expr &ctx input))

(calc &"123+456")
    "#,
        )
        .run_a0();
        assert_eq!(Some(579), output);
    }

    #[test]
    #[ignore] // This causes stack overflow and needs `RUST_MIN_STACK=104857600`.
    #[named]
    fn complex_program_stack() {
        let output = compile(
            function_name!(),
            r#"
    (include "library/prelude.scm")

    (struct Stack
        buffer: fixed-array[int 5]
        cursor: int)

    (fn Stack->push (self value)
        (array->set &(Stack->buffer self) (Stack->cursor self) value)
        (Stack->cursor= self (+ (Stack->cursor self) 1)))

    (fn Stack->top (self)
        (array->get &(Stack->buffer self) (- (Stack->cursor self) 1)))

    (fn Stack->pop (self)
        (if (>= (Stack->cursor self) 1)
            (begin
                (define value (Stack->top self))
                (Stack->cursor= self (- (Stack->cursor self) 1))
                value)
            0))

    (define stack (Stack (fixed-array 0 0 0 0 0) 0))
    (Stack->push &stack 42)
    (Stack->push &stack 43)
    (println-int (Stack->pop &stack))
    (println-int (Stack->pop &stack))
    (println-int (Stack->pop &stack))
    "#,
        )
        .run_raw_output();
        assert_eq!("43\n42\n0\n", output);
    }

    #[test]
    #[named]
    fn prelude_println_int() {
        let output = compile(
            function_name!(),
            r#"
(include "library/prelude.scm")

(println-int 12345)
"#,
        )
        .run_raw_output();
        assert_eq!("12345\n", output);
    }
}
