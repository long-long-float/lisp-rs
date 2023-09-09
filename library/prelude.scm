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

(fn println-int (value)
  (fn count-digit (value)
    (define digit 0)
    (for (i 1) (< 0 (/ value i)) (* i 10)
      (set! digit (+ digit 1)))
    digit)

  (define digit (count-digit value))
  (define buf (array->new digit))

  (define d 1)
  (for (i 0) (< i digit) (+ i 1) (begin
    (array->set buf i (% (/ value d) 10))
    (set! d (* d 10))))
  
  (for (i (- (array->len buf) 1)) (>= i 0) (- i 1) (begin
    (print-char (int->char (array->get buf i)))))
  (print "\n")
  (array->len buf))
