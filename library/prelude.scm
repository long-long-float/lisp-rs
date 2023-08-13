; Macros

(define-macro for (init condn update body)
  (list 'let 'loop (list init) 
    (list 'if condn (list 'begin
      body
      (list 'loop update)))))

; Functions

(fn print (str) (begin
  (syscall3 64 1 (array->data str) (array->len str))))

(fn println (str) (begin
  (print str)
  (print "\n")
  0))

(fn println-bool (val) (begin
  (println (if val "true" "false"))))