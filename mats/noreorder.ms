;;; noreorder.ms

; Actually, this behaviour is fine in rnrs and Chez, 
; but they show some incompatibilities with Racket.

(mat noreorder
  (equal?
    (with-output-to-string
      (lambda ()
        (car (list (display 1) (display 2)))))
    "12")
  )

(mat singleton
  (not (eq?
         (vector)
         (make-vector (random 1))))
  )
