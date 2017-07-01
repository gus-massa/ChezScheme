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

(include "../s/hamt.ss")

(define hash (lambda (v) (abs v)))
(define h1 ($hamt-set ($hamt-empty) 1 hash eq? 'a))
(define h2 ($hamt-set h1 2 hash eq? 'b))
(define h3 ($hamt-set h2 17 hash eq? 'c))
(define h4 ($hamt-set h3 -17 hash eq? 'd))
(define h5 ($hamt-remove h4 1 hash eq?))
(define h6 ($hamt-remove h5 17 hash eq?))

(mat hamt
    (equal? ($hamt-ref h1 1 hash eq? #f)
           'a)
    (equal? ($hamt-ref h1 2 hash eq? 'no)
           'no)
    (equal? ($hamt-ref h2 1 hash eq? #f)
           'a)
    (equal? ($hamt-ref h2 2 hash eq? #f)
           'b)
    (equal? ($hamt-ref h3 2 hash eq? #f)
           'b)
    (equal? ($hamt-ref h3 17 hash eq? #f)
           'c)
    (equal? ($hamt-ref h4 17 hash eq? #f)
           'c)
    (equal? ($hamt-ref h4 -17 hash eq? #f)
           'd)
    (equal? ($hamt-ref h5 1 hash eq? #f)
           #f)
    (equal? ($hamt-ref h5 2 hash eq? #f)
           'b)
    (equal? ($hamt-ref h5 17 hash eq? #f)
           'c)
    (equal? ($hamt-ref h6 17 hash eq? #f)
           #f)
    (equal? ($hamt-ref h6 2 hash eq? #f)
           'b)
    (equal? ($hamt-set h1 1 hash eq? 'a)
           h1)
    (equal? ($hamt-set h2 2 hash eq? 'b)
           h2)
    (equal? ($hamt-set h3 17 hash eq? 'c)
           h3)
    (equal? ($hamt-set h4 -17 hash eq? 'd)
           h4)
    (equal? ($hamt-count h1) 1)
    (equal? ($hamt-count h2) 2)
    (equal? ($hamt-count h3) 3)
    (equal? ($hamt-count h4) 4)
    (equal? ($hamt-count h5) 3)
  )
