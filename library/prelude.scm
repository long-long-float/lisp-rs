; Macros

(define-macro for (init condn update body)
  (define label (__gen-unique-sym))
  (list 'let label (list init) 
    (list 'if condn (list 'begin
      body
      (list label update)))))

; Functions

(fn print (str) (begin
  (syscall3 64 1 (array->data str) (array->len str))))

(fn println (str) (begin
  (print str)
  (print "\n")
  0))

(fn println-bool (val) (begin
  (println (if val "true" "false"))))