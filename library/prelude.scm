; Macros

(define-macro for (init condn update body)
  (define label (__gen-unique-sym))
  (list 'begin
    (list 'let label (list init) 
      (list 'if condn (list 'begin
        body
        (list label update))))
    0))

; Functions

(fn print (str)
  (syscall3 64 1 (array->data str) (array->len str)))

(fn println (str)
  (print str)
  (print "\n")
  0)

(fn println-bool (val)
  (println (if val "true" "false")))

(fn char->int (ch)
  (- (as ch int) (as #\0 int)))

(fn int->char (val)
  (as (+ (as #\0 int) val) char))

(fn print-char (ch)
  (define str " ")
  (array->set str 0 ch)
  (syscall3 64 1 (array->data str) (array->len str)))
