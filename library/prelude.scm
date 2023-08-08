(define-macro fn (name args body)
  (list 'define
        name 
        (list 'lambda args body)))

(define-macro for (init condn update body)
  (list 'let 'loop (list init) 
    (list 'if condn (list 'begin
      body
      (list 'loop update)))))
