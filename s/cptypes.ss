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

  (define-pass cptypes : Lsrc (ir ret types) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d) (when (number? d) (display (list d))) ir]
      [(ref ,maybe-src ,x)
       (guard (not (prelex-was-assigned x)))
       (let ([a (assoc x (unbox types))])
         (when a
           (set-box! ret (cdr a))))
       ir]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map cptypes e* r* t*)])
         (cond
           [(cond
              [(and (fx= (length e*) 1)
                    (eq? (primref-name pr) 'vector?)
                    (eq? (unbox (car r*)) 'vector?))
               (set-box! ret true-rec)
               (set-box! types (unbox (car t*)))
               (make-seq 'value/probably (car e*) true-rec)]
              [(and (fx= (length e*) 1)
                    (eq? (primref-name pr) 'vector-length))
               (set-box! ret 'fixnum?)
               (nanopass-case (Lsrc Expr) (car e*)
                 [(ref ,maybe-src ,x)
                  (guard (not (prelex-was-assigned x)))
                  (when (not (assoc x (unbox types)))
                    (set-box! types (cons (cons x 'vector?) (unbox types))))]
                 [else
                  (void)])
               #f]
              [(eq? (primref-name pr) 'vector)
               (set-box! ret 'vector?)
               #f]
              [else
                #f])]
           [else
            (for-each (lambda (t)
                        (for-each (lambda (a)
                                    (when (not (assoc (car a) (unbox types)))
                                      (set-box! types (cons a (unbox types)))))
                                  (unbox t)))
                      t*)
            `(call ,preinfo ,pr ,e* ...)]))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r0 (box #f)]
              [t0 (box (unbox types))]
              [e0 (cptypes e0 r0 t0)]
              [r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map cptypes e* r* t*)])
         (set-box! types (unbox t0))
         (for-each (lambda (t)
                     (for-each (lambda (a)
                                 (when (not (assoc (car a) (unbox types)))
                                   (set-box! types (cons a (unbox types)))))
                               (unbox t)))
                   t*)
         `(call ,preinfo ,e0 ,e* ...))]
      [(seq ,e1 ,e2)
       (let* ([e1 (cptypes e1 (box #f) types)]
              [e2 (cptypes e2 ret types)])
         (make-seq 'value/probably e1 e2))]
      [(if ,e1 ,e2 ,e3)
       (let* ([e1 (cptypes e1 (box #f) types)]
              [e2 (cptypes e2 (box #f) (box '()))]
              [e3 (cptypes e3 (box #f) (box '()))])
         `(if ,e1 ,e2 ,e3))]
      [(case-lambda ,preinfo ,cl* ...)
       (let ([cl* (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body (box #f) (box '()))])
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                       cl*)])
         `(case-lambda ,preinfo ,cl* ...))]
      [(letrec ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e r t)) e* r* t*)]
              [body (cptypes body ret types)])
         `(letrec ([,x* ,e*] ...) ,body))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r) (cptypes e r types)) e* r*)]
              [body (cptypes body ret types)])
         `(letrec* ([,x* ,e*] ...) ,body))]
      [(immutable-list (,e* ...) ,e)
       (let* ([t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e t) (cptypes e (box #f) t)) e* t*)]
              [e (cptypes e ret types)]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      #;[else ir]))

(lambda (x)
  (cptypes x (box #f) (box '())))
))
