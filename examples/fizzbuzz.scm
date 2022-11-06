(define fizzbuzz (lambda (x)
  (cond
   ((= (mod x 15) 0) "fizzbuzz")
   ((= (mod x 3) 0)  "fizz")
   ((= (mod x 5) 0)  "buzz")
   (#t (int->string x)))))

(let loop ((s 1) (e 50))
  (if (not (> s e))
    (begin 
      (print (fizzbuzz s))
      (loop (+ s 1) e))))
