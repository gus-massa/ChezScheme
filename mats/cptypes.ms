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
)
