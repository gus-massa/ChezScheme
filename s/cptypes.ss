"cptypes.ss"
;;; cptypes.ss
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

#|
Notes:
 - types is only a stub.
|#

(define $cptypes
(let ()
  (import (nanopass))
  (include "base-lang.ss")

  (with-output-language (Lsrc Expr)
    (define true-rec `(quote #t))
    (define false-rec `(quote #f))

    (define (simple? e) ;FIXME
      (nanopass-case (Lsrc Expr) e
        [(quote ,d) #t]
        [(ref ,maybe-src ,x) #t]
        [(case-lambda ,preinfo ,cl* ...) #t]
        [,pr #t]
        [(pariah) #t]
        [(moi) #t]
        [else #f]
        #;[else ($oops who "unrecognized record ~s" e)]))

    ; FIXME: Drop discardable operations in e1. 
    (define make-seq
      ; ensures that the right subtree of the output seq is not a seq if the
      ; second argument is similarly constrained, to facilitate result-exp
      (lambda (ctxt e1 e2)
        (if (simple? e1)
            e2
            (if (and (eq? ctxt 'effect) (simple? e2))
                e1
                (let ([e1 (nanopass-case (Lsrc Expr) e1
                            [(seq ,e11 ,e12)
                             (guard (simple? e12))
                             e11]
                            [else e1])])
                  (nanopass-case (Lsrc Expr) e2
                    [(seq ,e21 ,e22) `(seq (seq ,e1 ,e21) ,e22)]
                    [else `(seq ,e1 ,e2)]))))))

    (define make-seq* ; requires at least one operand
      (lambda (ctxt e*)
        (if (null? (cdr e*))
            (car e*)
            (make-seq ctxt (car e*) (make-seq* ctxt (cdr e*))))))
  )

  (define-pass cptypes : Lsrc (ir ret) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d) (when (number? d) (display (list d))) ir]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [e* (map cptypes e* r*)])
         (cond
           [(and (fx= (length e*) 1)
                 (eq? (primref-name pr) 'vector?)
                 (eq? (unbox (car r*)) 'vector?))
            (set-box! ret true-rec)
            (make-seq 'value/probably (car e*) true-rec)]
           [(eq? (primref-name pr) 'vector)
            (set-box! ret 'vector?)
            `(call ,preinfo ,pr ,e* ...)]
           [else
            `(call ,preinfo ,pr ,e* ...)]))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r0 (box #f)]
              [e0 (cptypes e0 r0)]
              [r* (map (lambda (e) (box #f)) e*)]
              [e* (map cptypes e* r*)])
         `(call ,preinfo ,e0 ,e* ...))]
      #;[else ir]))

(lambda (x)
  (cptypes x (box #f)))
))
