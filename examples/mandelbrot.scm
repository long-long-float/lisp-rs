; Reference https://gist.github.com/LeopoldTal/2aa79947c4cab728402c4054d6733254

(define MAX_ITERS 200)

(define get-rejection-iters (lambda (ptx pty)
    (let (
        [re 0.0]
        [im 0.0]
        [re-sq 0.0]
        [im-sq 0.0])
        (let loop ([nb-iters 0])
            (if (or (> (+ im-sq re-sq) 4.0) (>= nb-iters MAX_ITERS))
                nb-iters
                (begin
                    (set! im (+ (* 2.0 re im) pty))
                    (set! re (+ (- re-sq im-sq) ptx))
                    
                    (set! im-sq (* im im))
                    (set! re-sq (* re re))
                    (loop (+ nb-iters 1))))))))

(define palette (string->list ".:-=+*#%@"))

(define draw-point (lambda (x y)
    (let ([iters (get-rejection-iters x y)])
        (if (>= iters MAX_ITERS)
            (display #\ )
            (display (list-ref palette (mod (- iters 1) (length palette))))
            ))))

(let* (
    (step 0.045)
    (step-x (/ step 2))
    (step-y step)
    (lines 53)
    (columns 151)
    (center-x (- 0.6))
    (center-y 0)
    )
    (let loop1 ((cur-line 0)) (if (< cur-line lines)
        (let ((y (+ center-y (* step-y (- (* 0.5 lines) cur-line 0.5)))))
            (let loop2 ((cur-col 0)) (if (< cur-col columns)
                (let ((x (- center-x (* step-x (- (* 0.5 columns) cur-col 0.5)))))
                   (draw-point x y)
                   (loop2 (+ cur-col 1))
                )))
            (newline)
            (loop1 (+ cur-line 1)))
        )))
