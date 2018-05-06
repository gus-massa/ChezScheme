(display
  (+ 1 2)
)
(newline)
(newline)

(display
  (expand/optimize
    '(lambda (l b)
       (assv (unbox b) l))))
(newline)
(newline)

(display
  (expand/optimize
    '(lambda (l)
       (assv 5 l))))
(newline)
(newline)

(display
  (expand/optimize
    '(lambda (l)
       (assv 'a l))))
(newline)
(newline)


