(defun fizzbuzz (x)
  (cond
   ((zerop (mod x 15)) 'fizzbuzz)
   ((zerop (mod x 3))  'fizz)
   ((zerop (mod x 5))  'buzz)
   (T x)))

(defun fizzbuzz-solver (s e)
  (unless (> s e)
    (print (fizzbuzz s))
    (fizzbuzz-solver (+ s 1) e)))

(fizzbuzz-solver 1 50)