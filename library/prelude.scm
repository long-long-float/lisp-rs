(define-macro fn (name args body)
  (list 'define
        name 
        (list 'lambda args body)))