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

  (define-syntax context-case
    (lambda (x)
      (define predicate
        (lambda (type)
          (syntax-case type (app)
            [app #'app?]
            [_ (with-syntax ([type type])
                 #'(lambda (x) (eq? x 'type)))])))
      (syntax-case x (else)
        [(_ ctxt-exp [(type ...) e1 e2 ...] more ...)
         (with-syntax (((pred ...) (map predicate #'(type ...))))
           #'(let ((ctxt ctxt-exp))
               (if (or (pred ctxt) ...)
                   (begin e1 e2 ...)
                   (context-case ctxt more ...))))]
        [(_ ctxt-exp [else e1 e2 ...]) #'(begin e1 e2 ...)]
        [(_ ctxt-exp)
         #'($oops 'cptypes-internal "unexpected context ~s" ctxt-exp)])))

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

  (define (predicates-add/ref! types r pred)
    (nanopass-case (Lsrc Expr) r
      [(ref ,maybe-src ,x)
       (predicates-add! types x pred)]
      [else
       (void)]))

  (define (check-constant-is? x pred?)
    (nanopass-case (Lsrc Expr) x
      [(quote ,d) (pred? d)]
      [else #f]))

  (define (check-predicate-implies? x y)
    (and x
         y
         (or (eq? x y)
             (and (Lsrc? x)
                  (Lsrc? y)
                 (nanopass-case (Lsrc Expr) x
                   [(quote ,d1) 
                    (nanopass-case (Lsrc Expr) y
                      [(quote ,d2) (eq? d1 d2)] #;CHECK ;eq?/eqv?/equal?
                      [else #f])]
                   [else #f]))
             (cond
               [(eq? y 'vector?) (check-constant-is? x vector?)] 
               [(eq? y 'box?) (check-constant-is? x box?)] 
               [(eq? y 'number?) (check-constant-is? x number?)]
               [else #f]))))

  (define (check-predicate-implies-not? x y)
    ; for now this is enough
    (and x
         y
         (not (check-predicate-implies? x y))
         (not (check-predicate-implies? y x))))

  (define-pass cptypes : Lsrc (ir ctxt ret types) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d)
       (when (number? d)
        (display (list d)))
        (set-box! ret ir)
        ir]
      [(ref ,maybe-src ,x)
       (context-case ctxt
         [(test)
          (let ([t (predicates-lookup types x)])
            (cond
              [(check-predicate-implies-not? t false-rec) 
               (set-box! ret true-rec)
               true-rec]
              [(check-predicate-implies? t false-rec) 
               (set-box! ret false-rec)
                false-rec]
              [else
               (set-box! ret t)
               ir]))]
         [else
          (set-box! ret (predicates-lookup types x))
          ir])]
      [(seq ,[cptypes : e1 'effect (box #f) types -> e1] ,[cptypes : e2 ctxt ret types -> e2])
       (make-seq ctxt e1 e2)]
      [(if ,e1 ,e2 ,e3)
       (let* ([e1 (cptypes e1 'test (box #f) types)]
              [e2 (cptypes e2 ctxt (box #f) (predicates-copy types))]
              [e3 (cptypes e3 ctxt (box #f) (predicates-copy types))])
         `(if ,e1 ,e2 ,e3))]
      [(set! ,maybe-src ,x ,[cptypes : e 'value (box #f) types -> e])
       (set-box! ret void-rec)
       `(set! ,maybe-src ,x ,e)]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t)) e* r* t*)]
              [ir `(call ,preinfo ,pr ,e* ...)])
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         (cond
           [(and (fx= (length e*) 1)
                 (memq (primref-name pr) '(vector? box? number?)))
            (let ([pred (primref-name pr)]
                  [var (unbox (car r*))])
              (cond
                [(check-predicate-implies? var pred) 
                 (set-box! ret true-rec)
                 (make-seq ctxt (car e*) true-rec)]
                [(check-predicate-implies-not? var pred) 
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else ir]))]
           [(and (fx= (length e*) 1)
                 (eq? (primref-name pr) 'vector-length))
            (set-box! ret 'number?)
            (predicates-add/ref! types (car e*) 'vector?)
            ir]
           [(and (fx= (length e*) 1)
                 (eq? (primref-name pr) 'unbox))
            (predicates-add/ref! types (car e*) 'box?)
            ir]
           [(eq? (primref-name pr) 'vector)
            (set-box! ret 'vector?)
            ir]
           [(eq? (primref-name pr) 'box)
            (set-box! ret 'box?)
            ir]
           [else
            ir]))]
      [(case-lambda ,preinfo ,cl* ...)
       (let* ([r* (map (lambda (cl) (box #f)) cl*)]
              [t* (map (lambda (cl) (predicates-copy types)) cl*)]
              [x** (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body) x*]))
                       cl*)]
              [cl* (map (lambda (cl r t)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body 'value r t)]) #;FIXME
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                       cl* r* t*)])
         (context-case ctxt
           [(app/let) #;FIXME ;also for apply / call-with-values ?
            (when (fx= (length cl*) 1)
              (set-box! ret (unbox (car r*)))
              (predicates-merge! types (car t*) (car x**)))]
            [else (void)])
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t)) e* r* t*)]
              [e0 (nanopass-case (Lsrc Expr) e0
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)) ;move this part to case-lambda
                     (guard (fx= interface (length x*)))
                     (for-each (lambda (t) (predicates-merge! types t '())) t*)
                     (let ([subtypes (predicates-copy types)])
                       (for-each (lambda (x r) (predicates-add! subtypes x (unbox r)))
                                 x*
                                 r*)
                       (let ([e0 (cptypes e0 'app/let ret subtypes)])  #;FIXME
                         (predicates-merge! types subtypes x*)
                         e0))]
                    [(case-lambda ,preinfo ,cl* ...)
                     (for-each (lambda (t) (predicates-merge! types t '())) t*)
                     (cptypes e0 'app/let ret types)]  #;FIXME
                    [else
                      (let* ([r0 (box #f)]
                             [t0 (predicates-copy types)]
                             [e0 (cptypes e0 'value r0 t0)]) #;FIXME
                        (for-each (lambda (t) (predicates-merge! types t '())) t*)
                        (predicates-merge! types t0 '())
                        e0)])])
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t)) e* r* t*)])
         (for-each (lambda (t) (predicates-merge! types t x*)) t*)
         (let ([body (cptypes body ctxt ret types)])
           `(letrec ([,x* ,e*] ...) ,body)))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r) (cptypes e 'value r types)) e* r*)]
              [body (cptypes body ctxt ret types)])
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr ir]
      [(foreign ,conv ,name ,[cptypes : e 'value (box #f) types -> e] (,arg-type* ...) ,result-type)
       `(foreign ,conv ,name ,e (,arg-type* ...) ,result-type)]
      [(fcallable ,conv ,[cptypes : e 'value (box #f) types -> e] (,arg-type* ...) ,result-type)
       `(fcallable ,conv ,e (,arg-type* ...) ,result-type)]
      [(record ,rtd ,rtd-expr ,e* ...)
       (let* ([t-rtd-expr (predicates-copy types)]
              [rtd-expr (cptypes rtd-expr 'value (box #f) t-rtd-expr)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e 'value (box #f) t)) e* t*)])
         (predicates-merge! types t-rtd-expr '())
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e 'value (box #f) types -> e])
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can be reordered?
       (let* ([t1 (predicates-copy types)]
              [t2 (predicates-copy types)]
              [e1 (cptypes e1 'value (box #f) t1)]
              [e2 (cptypes e2 'value (box #f) t2)])
       (predicates-merge! types t1 '())
       (predicates-merge! types t2 '())
       `(record-set! ,rtd ,type ,index ,e1 ,e2))]
      [(record-type ,rtd ,[cptypes : e 'value (box #f) types -> e])
       `(record-type ,rtd ,e)]
      [(record-cd ,rcd ,rtd-expr ,[cptypes : e 'value (box #f) types -> e])
       `(record-cd ,rcd ,rtd-expr ,e)]
      [(immutable-list (,e* ...) ,e)
       (let* ([t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e 'value (box #f) t)) e* t*)]
              [e (cptypes e 'value ret types)]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      [(moi) ir]
      [(pariah) ir]
      [(cte-optimization-loc ,box0 ,[cptypes : e 'value (box #f) types -> e]) ;don't shadow box
       `(cte-optimization-loc ,box0 ,e)]
      [(cpvalid-defer ,e) (sorry! who "cpvalid leaked a cpvalid-defer form ~s" ir)]
      [(profile ,src) ir]
      [else ($oops who "unrecognized record ~s" ir)]
      #;[else ir]))

(lambda (x)
  (cptypes x 'value (box #f) (predicates-new)))
))
