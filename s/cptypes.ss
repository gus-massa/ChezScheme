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
    (define void-rec `(quote ,(void)))
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

  (define (predicates-new)
    (box '()))

  (define (predicates-copy types)
    (box (unbox types)))

  (define (predicates-add! types x type)
    (when (not (prelex-was-assigned x))
          (not (assoc x (unbox types)))
          (set-box! types (cons (cons x type) (unbox types)))))

  (define (predicates-merge! types from skiped)
    (let ([base (unbox types)]) ;try to avoid common part
      (let loop ([from (unbox from)])
        (when (and (not (null? from))
                    (not (eq? from base)))
          (let ([a (car from)])
            (unless (member (car a) skiped)
              (predicates-add! types (car a) (cdr a))))
          (loop (cdr from))))))

  (define (predicates-lookup types x)
    (and (not (prelex-was-assigned x))
         (let ([a (assoc x (unbox types))])
           (and a (cdr a)))))

  (define-pass cptypes : Lsrc (ir ret types) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d) (when (number? d) (display (list d))) ir]
      [(ref ,maybe-src ,x)
       (set-box! ret (predicates-lookup types x))
       ir]
      [(seq ,[cptypes : e1 (box #f) types -> e1] ,[cptypes : e2 (box #f) types -> e2])
       (make-seq 'value/probably e1 e2)]
      [(if ,e1 ,e2 ,e3)
       (let* ([e1 (cptypes e1 (box #f) types)]
              [e2 (cptypes e2 (box #f) (predicates-copy types))]
              [e3 (cptypes e3 (box #f) (predicates-copy types))])
         `(if ,e1 ,e2 ,e3))]
      [(set! ,maybe-src ,x ,[cptypes : e (box #f) types -> e])
       (set-box! ret void-rec)
       `(set! ,maybe-src ,x ,e)]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map cptypes e* r* t*)])
         (cond
           [(cond
              [(and (fx= (length e*) 1)
                    (eq? (primref-name pr) 'vector?)
                    (eq? (unbox (car r*)) 'vector?))
               (set-box! ret true-rec)
               (predicates-merge! types (car t*) '())
               (make-seq 'value/probably (car e*) true-rec)]
              [(and (fx= (length e*) 1)
                    (eq? (primref-name pr) 'vector-length))
               (set-box! ret 'fixnum?)
               (nanopass-case (Lsrc Expr) (car e*)
                 [(ref ,maybe-src ,x)
                  (predicates-add! types x 'vector?)]
                 [else
                  (void)])
               #f]
              [(eq? (primref-name pr) 'vector)
               (set-box! ret 'vector?)
               #f]
              [else
                #f])]
           [else
            (for-each (lambda (t) (predicates-merge! types t '())) t*)
            `(call ,preinfo ,pr ,e* ...)]))]
      [(case-lambda ,preinfo ,cl* ...)
       (let ([cl* (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body (box #f) (predicates-copy types))])
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                       cl*)])
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r0 (box #f)]
              [t0 (predicates-copy types)]
              [e0 (cptypes e0 r0 t0)]
              [r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map cptypes e* r* t*)])
         (predicates-merge! types t0 '())
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e r t)) e* r* t*)])
         (for-each (lambda (t) (predicates-merge! types t x*)) t*)
         (let ([body (cptypes body ret types)])
           `(letrec ([,x* ,e*] ...) ,body)))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r) (cptypes e r types)) e* r*)]
              [body (cptypes body ret types)])
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr ir]
      [(foreign ,conv ,name ,[cptypes : e (box #f) types -> e] (,arg-type* ...) ,result-type)
       `(foreign ,conv ,name ,e (,arg-type* ...) ,result-type)]
      [(fcallable ,conv ,[cptypes : e (box #f) types -> e] (,arg-type* ...) ,result-type)
       `(fcallable ,conv ,e (,arg-type* ...) ,result-type)]
      [(record ,rtd ,rtd-expr ,e* ...)
       (let* ([t-rtd-expr (predicates-copy types)]
              [rtd-expr (cptypes rtd-expr (box #f) t-rtd-expr)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e (box #f) t)) e* t*)])
         (predicates-merge! types t-rtd-expr '())
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e (box #f) types -> e])
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can be reordered?
       (let* ([t1 (predicates-copy types)]
              [t2 (predicates-copy types)]
              [e1 (cptypes e1 (box #f) t1)]
              [e2 (cptypes e2 (box #f) t2)])
       (predicates-merge! types t1 '())
       (predicates-merge! types t2 '())
       `(record-set! ,rtd ,type ,index ,e1 ,e2))]
      [(record-type ,rtd ,[cptypes : e (box #f) types -> e])
       `(record-type ,rtd ,e)]
      [(record-cd ,rcd ,rtd-expr ,[cptypes : e (box #f) types -> e])
       `(record-cd ,rcd ,rtd-expr ,e)]
      [(immutable-list (,e* ...) ,e)
       (let* ([t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e (box #f) t)) e* t*)]
              [e (cptypes e ret types)]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      [(moi) ir]
      [(pariah) ir]
      [(cte-optimization-loc ,box0 ,[cptypes : e (box #f) types -> e]) ;don't shadow box
       `(cte-optimization-loc ,box0 ,e)]
      [(cpvalid-defer ,e) (sorry! who "cpvalid leaked a cpvalid-defer form ~s" ir)]
      [(profile ,src) ir]
      [else ($oops who "unrecognized record ~s" ir)]
      #;[else ir]))

(lambda (x)
  (cptypes x (box #f) (predicates-new)))
))
