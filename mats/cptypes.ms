;;; cptypes.ms
;;; Copyright 1984-2017 Cisco Systems, Inc.
;;; 
;;; Licensed under the Apache License, Version 2.0 (the "License");
;;; you may not use this file except in compliance with the License.
;;; You may obtain a copy of the License at
;;; 
;;; http://www.apache.org/licenses/LICENSE-2.0
;;; 
;;; Unless required by applicable law or agreed to in writing, software
;;; distributed under the License is distributed on an "AS IS" BASIS,
;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;; See the License for the specific language governing permissions and
;;; limitations under the License.

(define-syntax cptypes-equivalent-expansion?
  (syntax-rules ()
    [(_ x y)
     (equivalent-expansion?
      (parameterize ([enable-cp0 #t]
                     [#%$suppress-primitive-inlining #f]
                     #;[optimize-level (max (optimize-level) 2)])
        (expand/optimize x))
      (parameterize ([enable-cp0 #t]
                     [#%$suppress-primitive-inlining #f]
                     #;[optimize-level (max (optimize-level) 2)])
        (expand/optimize y)))]))

(mat cptypes-handcoded
  (cptypes-equivalent-expansion?
    '(vector? (vector))  ;actually reduced by folding, not cptypes 
    #t)
  (cptypes-equivalent-expansion?
    '(vector? (vector 1 2 3)) 
    #t)
  (cptypes-equivalent-expansion?
    '(vector? (box 1)) 
    #f)
  (cptypes-equivalent-expansion?
    '(box? (vector 1 2 3)) 
    #f)
  (cptypes-equivalent-expansion?
    '(box? (box 1)) 
    #t)
  (cptypes-equivalent-expansion?
    '(pair? (cons 1 2)) 
    #t)
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (vector? x))
    '(lambda (x) (vector-length x) #t))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (box? x))
    '(lambda (x) (vector-length x) #f))
  (cptypes-equivalent-expansion?
    '(lambda (x) (if (zero? (vector-length x)) (newline) (void)) (vector? x))
    '(lambda (x) (if (zero? (vector-length x)) (newline) (void)) #t))
  (not (cptypes-equivalent-expansion?
         '(lambda (x) (if (zero? (random 2)) (vector-length x) (void)) (vector? x))
         '(lambda (x) (if (zero? (random 2)) (vector-length x) (void)) #t)))
  (not (cptypes-equivalent-expansion?
         '(lambda (x) (if (zero? (random 2)) (void) (vector-length x)) (vector? x))
         '(lambda (x) (if (zero? (random 2)) (void) (vector-length x)) #t)))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (if x (newline) (void)))
    '(lambda (x) (vector-length x) (if #t (newline) (void))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (if (vector? x) (newline) (void)))
    '(lambda (x) (vector-length x) (if #t (newline) (void))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (when (vector? x) (if x (newline) (void))))
    '(lambda (x) (when (vector? x) (if #t (newline) (void)))))
  (not (cptypes-equivalent-expansion?
         '(lambda (x) (when (boolean? x) (if x (newline) (void))))
         '(lambda (x) (when (boolean? x) (if #t (newline) (void))))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (if (zero? (random 2)) (vector? x) (void)))
    '(lambda (x) (vector-length x) (if (zero? (random 2)) #t (void))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (if (zero? (random 2)) (void) (vector? x)))
    '(lambda (x) (vector-length x) (if (zero? (random 2)) (void) #t)))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (vector-length x) (set! y (vector? x)))
    '(lambda (x y) (vector-length x) (set! y #t)))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (set! y (vector-length x)) (vector? x))
    '(lambda (x y) (set! y (vector-length x)) #t))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (let ([y (random 7)]) (list (vector? x) y y)))
    '(lambda (x) (vector-length x) (let ([y (random 7)]) (list #t y y))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (vector-length x) (let ([y (vector? x)]) (list (random 7) y y)))
    '(lambda (x) (vector-length x) (let ([y #t]) (list (random 7) y y))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (let ([y (vector-length x)]) (list (vector? x) y y)))
    '(lambda (x) (let ([y (vector-length x)]) (list #t y y))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (let ([y (vector-length x)])
                   (let ([z (vector? x)])
                     (list y y z z))))
    '(lambda (x) (let ([y (vector-length x)])
                   (let ([z #t])
                     (list y y z z)))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (let ([y (vector-length x)]) (display (list y y))) (vector? x))
    '(lambda (x) (let ([y (vector-length x)]) (display (list y y))) #t))
  (cptypes-equivalent-expansion?
    '(lambda (x) (let ([y (random 7)]) (display (list (vector-length x) y y))) (vector? x))
    '(lambda (x) (let ([y (random 7)]) (display (list (vector-length x) y y))) #t))
  (cptypes-equivalent-expansion?
    '(let ([y (vector 1 2 3)]) (display (list (vector? y) y y)))
    '(let ([y (vector 1 2 3)]) (display (list #t y y))))
  (cptypes-equivalent-expansion?
    '(let ([y (vector 1 2 3)]) (display (list y y)) (vector? y))
    '(let ([y (vector 1 2 3)]) (display (list y y)) #t))
  (cptypes-equivalent-expansion?
    '(vector? (let ([y (vector 1 2 3)]) (display (list y y)) y))
    '(begin (let ([y (vector 1 2 3)]) (display (list y y)) y) #t))
  (cptypes-equivalent-expansion?
    '(vector? (let ([y (vector 1 2 3)]) (display (list y y)) (vector 4 5 6)))
    '(begin (let ([y (vector 1 2 3)]) (display (list y y)) (vector 4 5 6)) #t))
  (cptypes-equivalent-expansion?
    '(lambda (x) (if (vector? x) (vector? x) (void)))
    '(lambda (x) (if (vector? x) #t (void))))
  (not (cptypes-equivalent-expansion?
         '(lambda (x) (if (vector? x) (void) (vector? x)))
         '(lambda (x) (if (vector? x) (void) #t))))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (if (vector? x) (if (vector? y) (list (vector? x) (vector? y)) (void)) (void)))
    '(lambda (x y) (if (vector? x) (if (vector? y) (list #t #t) (void)) (void))))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (if (and (vector? x) (vector? y)) (list (vector? x) (vector? y)) (void)))
    '(lambda (x y) (if (and (vector? x) (vector? y)) (list #t #t) (void))))
  (not (cptypes-equivalent-expansion?
         '(lambda (x y) (if (or (vector? x) (vector? y)) (vector? x) (void)))
         '(lambda (x y) (if (or (vector? x) (vector? y)) #t (void)))))
  (not (cptypes-equivalent-expansion?
         '(lambda (x y) (if (or (vector? x) (vector? y)) (vector? y) (void)))
         '(lambda (x y) (if (or (vector? x) (vector? y)) #t (void)))))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (if (if (vector? x) (vector? y) #f) (list (vector? x) (vector? y)) (void)))
    '(lambda (x y) (if (if (vector? x) (vector? y) #f) (list #t #t) (void))))
  (cptypes-equivalent-expansion?
    '(lambda (x y) (if (if (vector? x) (vector? y) #t) (void) (vector? x)))
    '(lambda (x y) (if (if (vector? x) (vector? y) #t) (void) #t)))
  (cptypes-equivalent-expansion?
    '(begin (error 'who "msg") (display 1)) ;could be reduced in cp0
    '(begin (error 'who "msg") (display 2)))
  (cptypes-equivalent-expansion?
    '(if (error 'who "msg") (display 1) (display 2))
    '(if (error 'who "msg") (display -1) (display -2)))
  (cptypes-equivalent-expansion?
    '(begin (if (error 'who "msg") (display 1) (display 2)) (display 3))
    '(begin (if (error 'who "msg") (display 1) (display 2)) (display -3)))
  (cptypes-equivalent-expansion?
    '(begin (if (box? (box 0)) (error 'who "msg") (void)) (display 1))
    '(begin (if (box? (box 0)) (error 'who "msg") (void)) (display -1)))
  (not (cptypes-equivalent-expansion?
         '(begin (if (box? (box 0)) (void) (error 'who "msg")) (display 1))
         '(begin (if (box? (box 0)) (void) (error 'who "msg")) (display -1))))
  (cptypes-equivalent-expansion?
    '(lambda (x) (if (zero? (random 2)) (vector-length x) (error 'who "msg")) (vector? x))
    '(lambda (x) (if (zero? (random 2)) (vector-length x) (error 'who "msg")) #t))
  (cptypes-equivalent-expansion?
    '(lambda (x) (if (zero? (random 2)) (error 'who "msg") (vector-length x)) (vector? x))
    '(lambda (x) (if (zero? (random 2)) (error 'who "msg") (vector-length x)) #t))
  (cptypes-equivalent-expansion?
    '(begin (if (zero? (random 2)) (error 'who "msg") (error 'who "other")) (display 1))
    '(begin (if (zero? (random 2)) (error 'who "msg") (error 'who "other")) (display -1)))
)

(define (test-chain l)
  (let loop ([l l])
    (if (null? l)
        #t
        (and (let loop ([t (cdr l)])
               (if (null? t)
                   #t
                   (and (cptypes-equivalent-expansion?
                          `(lambda (x) (when (,(car l) x) (,(car t) x)))
                          `(lambda (x) (when (,(car l) x) #t)))
                        (not (cptypes-equivalent-expansion?
                               `(lambda (x) (when (,(car t) x) (,(car l) x)))
                               `(lambda (x) (when (,(car t) x) #t))))
                        (loop (cdr t)))))
             (loop (cdr l))))))

(define (test-disjoint l)
  (let loop ([l l])
    (if (null? l)
        #t
       (and (cptypes-equivalent-expansion?
              `(lambda (x) (when (,(car l) x) (,(car l) x)))
              `(lambda (x) (when (,(car l) x) #t)))
            (let loop ([t (cdr l)])
              (if (null? t)
                  #t
                  (and (cptypes-equivalent-expansion?
                         `(lambda (x) (when (,(car l) x) (,(car t) x)))
                         `(lambda (x) (when (,(car l) x) #f)))
                       (cptypes-equivalent-expansion?
                         `(lambda (x) (when (,(car t) x) (,(car l) x)))
                         `(lambda (x) (when (,(car t) x) #f)))
                       (loop (cdr t)))))
            (loop (cdr l))))))

(mat cptypes-type-implies?
  (test-chain '(fixnum? integer? number?))
  (test-chain '(gensym? symbol?))
  (test-chain '(not boolean?))
  (test-disjoint '(pair? box? record? number? vector? string? bytevector? fxvector? symbol? char? boolean? null?))
  (test-disjoint '(pair? box? integer? gensym? not))
  (test-disjoint '(pair? box? fixnum?))
)
