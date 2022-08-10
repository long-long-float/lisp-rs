(define fizzbuzz (lambda (x)
  (cond
   ((= (mod x 15) 0) 'fizzbuzz)
   ((= (mod x 3) 0)  'fizz)
   ((= (mod x 5) 0)  'buzz)
   (#t x))))

(let loop ((s 1) (e 50))
  (unless (> s e)
    (print (fizzbuzz s))
    (loop (+ s 1) e)))
