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
    '(lambda (x) (vector-length x) (vector? x))
    '(lambda (x) (vector-length x) #t))
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
    '(lambda (x) (vector-length x) (if (vector? x) (newline) (void)))
    '(lambda (x) (vector-length x) (if #t (newline) (void))))
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
)
