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

(fn parse-spaces (ctx input)
    (for (i (Context->cursor ctx)) 
        (and (= (array->get input i) #\ ) (< i (array->len input))) 
        (+ i 1)
        (Context->cursor= ctx (+ (Context->cursor ctx) 1)))
    0)

(fn calc-expr (ctx input)
    (define left (parse-int ctx input))
    (parse-spaces ctx input)
    (define op (parse-op ctx input))
    (parse-spaces ctx input)
    (define right (parse-int ctx input))
    (cond
        ((= op #\+) (+ left right))
        ((= op #\-) (- left right))
        (#t 0)))

(fn calc (input)
    (define ctx (Context 0))
    (calc-expr &ctx input))

(calc &"10 + 20")
