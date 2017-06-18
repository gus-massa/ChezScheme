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
 - (cptypes ir ctxt ret types t-types f-types)
   ir: expression to be optimized
   <return value>: the optimized expression
   
   ctxt: 'effect 'value 'app/let
         (TODO: replace 'app/let with an app record like in cp0)
   ret: a box, to return the type of the result of the expression
   types: a "predicates" record. Actually just a box with an assoc, but let's
          pretend it's something fancy and manipulate it using only the API.
          It has the associations of prelex to types that were discovered before
          and it is possible to add more association that will be used in the
          following expressions.
          (box ((x . 'pair?) (y . 'vector) (z . `(quote 0))))
   t-types: like types, but it also has the types that should be used in case
            the expression is not a #f, so these types will be used in the 
            "then" branch of an if.
            It may be #f to signal that we don't care. This is automatically
            handle in the "predicates" function.
   f-types: idem for the "else" branch. (if x (something) (here x is #f))


 - predicate: (each one, not the record)
              They may be:
              * a symbol to indicate the type, like 'vector? 'pair? 'number?
                (there are a few fake values, in particular 'bottom? is used to
                 signal that there is an error)
              * a nanopass-quoted value that is okay-to-copy?, like
                `(quote 0) `(quote 5) `(quote #t) `(quote '())
                (this includes `(quote <record-type-descriptor?>))
              * TODO: add something to indicate that x is a record of that type
              * TODO: add something to indicate that x is a procedure to 
                      create/setter/getter/predicate of a record of that type
              * TODO: add primitives, probably the nanopass version of pr
              * TODO: add procedure? and perhaps some minimal signature for them
                  
              
 - most of the time I'm using eq? and eqv? as if they were equivalent.
   this is not a good idea.
 - most FIXME are not bugs but sites were the code can be improved. 
 - most CHECK are parts where I'm not sure that it is correct. 
 
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
    (define null-rec `(quote ()))
    (define empty-vector-rec `(quote #()))
    (define empty-string-rec `(quote ""))
    (define empty-bytevector-rec `(quote #vu8()))
    (define empty-fxvector-rec `(quote #vfx()))
    (define eof-rec `(quote #!eof))
    (define bwp-rec `(quote #!bwp))

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
    (and types
         (box (unbox types))))

  (define (predicates-add! types x type)
    (when (and types
               type
               (not (eq? type 'ptr?))
               (not (prelex-was-assigned x))
               (not (assoc x (unbox types))))
      (set-box! types (cons (cons x type) (unbox types)))))

  (define (predicates-merge! types from skipped)
    (when (and types from)
      (let ([base (unbox types)]) ;try to avoid common part
        (let loop ([from (unbox from)])
          (when (and (not (null? from))
                     (not (eq? from base)))
            (let ([a (car from)])
              (unless (member (car a) skipped)
                (predicates-add! types (car a) (cdr a))))
            (loop (cdr from)))))))

  (define (predicates-lookup types x)
    (and types
         (not (prelex-was-assigned x))
         (let ([a (assoc x (unbox types))])
           (and a (cdr a)))))

  (define (predicates-add/ref! types r pred)
    (nanopass-case (Lsrc Expr) r
      [(ref ,maybe-src ,x)
       (predicates-add! types x pred)]
      [else
       (void)]))

  (define okay-to-copy?
    (lambda (obj)
      ; okay to copy obj if (eq? (faslin (faslout x)) x) => #t or (in the case of numbers and characters)
      ; the value of (eq? x x) is unspecified
      (or (symbol? obj)
          (number? obj)
          (char? obj)
          (boolean? obj)
          (null? obj)
          (eqv? obj "")
          (eqv? obj '#())
          (eqv? obj '#vu8())
          (eqv? obj '#vfx())
          (eq? obj (void))
          (eof-object? obj)
          (bwp-object? obj)
          (eq? obj '#6=#6#)
          ($unbound-object? obj)
          (record-type-descriptor? obj))))

  (define (datum->predicate d ir)
    (cond
      [(okay-to-copy? d) ir]
      [(pair? d) 'pair?]
      [(box? d) 'box?]
      [(vector? d) 'vector?]
      [(string? d) 'string?]
      [(bytevector? d) 'bytevector?]
      [(fxvector? d) 'fxvector?]
      [else #f]))

  (define (primref-name->predicate name extend?)
    (case name
      [(pair? box?
        record? record-type-descriptor?
        fixnum? integer? number?
        vector? string? bytevector? fxvector?
        gensym? symbol?
        char?
        bottom? ptr?  ;pseudo-predicates
        boolean?)
        name]
      [void? void-rec] ;fake-predicate
      #;[true-object? true-rec]
      [not false-rec]
      #;[not? false-rec]
      [null? null-rec]
      [eof-object? eof-rec]
      [bwp-object? bwp-rec]
      #;[$?self?? "'#6=#6#"-rec] ;???
      #;[$unbound-object? unbound-rec] ;???
      #;[vector-empty? empty-vector-rec]
      #;[string-empty? empty-string-rec]
      #;[bytevector-empty? empty-bytevector-rec]
      #;[fxvector-empty? empty-fxvector-rec]
      [(not extend?) #f] ;---------------------------------------------------
      [(bit? length? ufixnum? pfixnum?) 'fixnum?]
      [(sint? uint? exact-integer?) 'integer?] ;perhaps use exact-integer? 
      [(uinteger?) 'integer?]
      [(flonum? rational? real? cflonum?) 'number?]
      [else #f]))

  (define (primref->predicate pr)
    (primref-name->predicate (primref-name pr) #f))

  (define (check-constant-is? x pred?)
    (nanopass-case (Lsrc Expr) x
      [(quote ,d) (pred? d)]
      [else #f]))

  ; strange properties of bottom? here:
  ; (implies? x bottom?): only for x=bottom?
  ; (implies? bottom? y): allways
  ; (implies-not? x bottom?): never
  ; (implies-not? bottom? y): never
  ; check (implies? x bottom?) before (implies? x something?)
  (define (check-predicate-implies? x y)
    (and x
         y
         (or (eq? x y)
             (and (Lsrc? x)
                  (Lsrc? y)
                  (nanopass-case (Lsrc Expr) x
                    [(quote ,d1) 
                     (nanopass-case (Lsrc Expr) y
                       [(quote ,d2) (eqv? d1 d2)] #;CHECK ;eq?/eqv?/equal?
                       [else #f])]
                    [else #f]))
             (eq? x 'bottom?)
             (cond
               #;[(eq? y 'pair?) (check-constant-is? x pair?)] 
               #;[(eq? y 'box?) (check-constant-is? x box?)] 
               [(eq? y 'fixnum?) (check-constant-is? x target-fixnum?)]
               [(eq? y 'integer?) (or (eq? x 'fixnum?)
                                      (check-constant-is? x integer?))]
               [(eq? y 'number?) (or (eq? x 'fixnum?)
                                     (eq? x 'integer?)
                                     (check-constant-is? x number?))]
               [(eq? y 'vector?) (check-constant-is? x vector?)] 
               [(eq? y 'string?) (check-constant-is? x string?)]
               [(eq? y 'bytevector?) (check-constant-is? x bytevector?)]
               [(eq? y 'fxvector?) (check-constant-is? x fxvector?)] 
               [(eq? y 'gensym?) (check-constant-is? x gensym?)] 
               [(eq? y 'symbol?) (or (eq? x 'gensym?)
                                     (check-constant-is? x symbol?))] 
               [(eq? y 'char?) (check-constant-is? x char?)] 
               [(eq? y 'boolean?) (or (check-constant-is? x not)
                                      (check-constant-is? x (lambda (x) (eq? x #t))))]
               [(eq? y 'record?) (or (eq? x 'record-type-descriptor?)
                                     (check-constant-is? x record?))] 
               [(eq? y 'record-type-descriptor?) (check-constant-is? x record-type-descriptor?)] 
               [(eq? y 'ptr?) #t]
               [else #f]))))

  (define (check-predicate-implies-not? x y)
    ; for now this is enough
    (and x
         y
         (not (check-predicate-implies? x y))
         (not (check-predicate-implies? y x))))

  (define (symbol-append . x)
    (string->symbol
     (apply string-append (map symbol->string x))))  

  (define (signature->result-predicate signature)
    (let ([result (cadr signature)])
      (cond
        [(symbol? result)
         (primref-name->predicate (symbol-append result '?) #t)]
        [(pair? result)
         (primref-name->predicate 'pair? #t)]
        [else
         #f])))

  (define (primref->result-predicate pr)
    (cond
      [(all-set? (prim-mask abort-op)
                 (primref-flags pr))
       (primref-name->predicate 'bottom? #t)]
      [else
       (let ([signatures (primref-signatures pr)])
         (and (>= (length signatures) 1)
              (let* ([results (map signature->result-predicate signatures)]
                     [first-result (car results)])
                (and (andmap (lambda (result) ;TODO: Get a better union of multiple results
                              (check-predicate-implies? result first-result))
                             results)
                     first-result))))]))

  (define (signature->argument-predicate signature pos)
    (let* ([arguments (car signature)]
           [dots (memq '... arguments)])
      (cond
        [(and dots (null? (cdr dots)))
         (cond
           [(< pos (- (length arguments) 2))
            (primref-name->predicate
             (symbol-append (list-ref arguments pos) '?)
             #t)]
           [else
            (primref-name->predicate 
              (symbol-append (list-ref arguments (- (length arguments) 2)) '?)
              #t)])]
         [dots #f] ;FIXME
         [else
          (cond
            [(< pos (length arguments))
             (let ([argument (list-ref arguments pos)])
               (if (pair? argument)
                   (primref-name->predicate 'pair? #t)
                   (primref-name->predicate (symbol-append argument '?) #t)))]
            [else
             (primref-name->predicate 'bottom? #t)])])))

  (define (primref->argument-predicate pr pos)
    (let ([signatures (primref-signatures pr)])
      (and (>= (length signatures) 1)
           (let* ([vals (map (lambda (signature)
                              (signature->argument-predicate signature pos))
                             signatures)]
                  [first-val (car vals)])
             (and (andmap (lambda (val) ;TODO: Get a better union of multiple vals
                            (check-predicate-implies? val first-val))
                          vals)
                  first-val)))))

  (define-pass cptypes : Lsrc (ir ctxt ret types t-types f-types) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d)
       (set-box! ret (datum->predicate d ir))
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
               (predicates-add! f-types x false-rec)
               ir]))]
         [else
           (let ([t (predicates-lookup types x)])
               (set-box! ret t)
            (cond
              [(Lsrc? t)
               (nanopass-case (Lsrc Expr) t
                 [(quote ,d) t]
                 [else ir])]
               [else ir]))])]
      [(seq ,e1 ,e2)
       (let* ([r1 (box #f)]
              [e1 (cptypes e1 'effect r1 types #f #f)])
         (cond 
           [(check-predicate-implies? (unbox r1) 'bottom?)
            (set-box! ret (unbox r1))
            e1]
           [else 
            (let ([e2 (cptypes e2 ctxt ret types t-types f-types)])
              (make-seq ctxt e1 e2))]))]
      [(if ,e1 ,e2 ,e3)
       (let* ([r1 (box #f)]
              [t-types1 (predicates-copy types)]
              [f-types1 (predicates-copy types)]
              [e1 (cptypes e1 'test r1 types t-types1 f-types1)])
         (cond
           [(check-predicate-implies? (unbox r1) 'bottom?) ;check bottom first
            (set! ret (unbox r1))
            e1]
           [(check-predicate-implies-not? (unbox r1) false-rec)
            (predicates-merge! t-types t-types1 '())
            (predicates-merge! f-types t-types1 '())
            (let ([e2 (cptypes e2 ctxt ret t-types1 t-types f-types)])
              (make-seq ctxt e1 e2))]
           [(check-predicate-implies? (unbox r1) false-rec)
            (predicates-merge! t-types f-types1 '())
            (predicates-merge! f-types f-types1 '())
            (let ([e3 (cptypes e3 ctxt ret f-types1 t-types f-types)])
              (make-seq ctxt e1 e3))]
           [else
            (let* ([r2 (box #f)]
                   [t-types2 (predicates-copy t-types1)]
                   [f-types2 (predicates-copy t-types1)]
                   [e2 (cptypes e2 ctxt r2 t-types1 t-types2 f-types2)]
                   [r3 (box #f)]
                   [t-types3 (predicates-copy f-types1)]
                   [f-types3 (predicates-copy f-types1)]
                   [e3 (cptypes e3 ctxt r3 f-types1 t-types3 f-types3)])
              (cond
                [(check-predicate-implies? (unbox r2) 'bottom?) ;check bottom first
                 (predicates-merge! t-types t-types3 '())
                 (predicates-merge! f-types f-types3 '())
                 (predicates-merge! types f-types1 '())]
                [(check-predicate-implies-not? (unbox r2) false-rec)
                 (predicates-merge! f-types f-types3 '())]
                [(check-predicate-implies? (unbox r2) false-rec)
                 (predicates-merge! t-types t-types3 '())])
              (cond
                [(check-predicate-implies? (unbox r3) 'bottom?) ;check bottom first
                 (predicates-merge! t-types t-types2 '())
                 (predicates-merge! f-types f-types2 '())
                 (predicates-merge! types t-types1 '())]
                [(check-predicate-implies-not? (unbox r3) false-rec)
                 (predicates-merge! f-types f-types2 '())]
                [(check-predicate-implies? (unbox r3) false-rec)
                 (predicates-merge! t-types t-types2 '())])
              (cond #;FIXME
                [(check-predicate-implies? (unbox r2) (unbox r3)) 
                 (set-box! ret (unbox r3))]
                [(check-predicate-implies? (unbox r3) (unbox r2)) 
                 (set-box! ret (unbox r2))]
                [else (void)])
              `(if ,e1 ,e2 ,e3))]))]
      [(set! ,maybe-src ,x ,[cptypes : e 'value (box #f) types #f #f -> e])
       (set-box! ret void-rec)
       `(set! ,maybe-src ,x ,e)]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f)) e* r* t*)]
              [ir `(call ,preinfo ,pr ,e* ...)])
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         (set-box! ret (primref->result-predicate pr))
         (for-each (lambda (e n)
                     (let ([pred (primref->argument-predicate pr n)])
                       (predicates-add/ref! types e pred)
                       (predicates-add/ref! t-types e pred)
                       (predicates-add/ref! f-types e pred)))
                   e*
                   (enumerate e*))
         (primref->argument-predicate pr 0)
         (cond
           [(and (fx= (length e*) 2)
                 (or (eq? (primref-name pr) 'eq?)
                     (eq? (primref-name pr) 'eqv?)))
              (let ([r1 (car r*)]
                    [r2 (cadr r*)]
                    [e1 (car e*)]
                    [e2 (cadr e*)])
              (cond
                [(or (check-predicate-implies-not? (unbox r1) (unbox r2))
                     (check-predicate-implies-not? (unbox r2) (unbox r1)))
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect e1 e2) false-rec)]
                [else
                 (predicates-add/ref! t-types e1 (unbox r2))
                 (predicates-add/ref! t-types e2 (unbox r1))
                 ir]))]
           [(and (fx= (length e*) 1)
                 (primref->predicate pr))
            (let ([pred (primref->predicate pr)]
                  [var (unbox (car r*))])
              (cond
                [(check-predicate-implies? var pred) 
                 (set-box! ret true-rec)
                 (make-seq ctxt (car e*) true-rec)]
                [(check-predicate-implies-not? var pred) 
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else  
                 (predicates-add/ref! t-types (car e*) pred)
                 ir]))]
           [else
            ir]))]
      [(case-lambda ,preinfo ,cl* ...)
       (let* ([r* (map (lambda (cl) (box #f)) cl*)]
              [t* (map (lambda (cl) (predicates-copy types)) cl*)]
              [t-t* (map (lambda (cl) (predicates-copy t-types)) cl*)]
              [f-t* (map (lambda (cl) (predicates-copy f-types)) cl*)]
              [x** (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body) x*]))
                       cl*)]
              [cl* (map (lambda (cl r t t-t f-t)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body 'value r t t-t f-t)]) #;FIXME
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                       cl* r* t* t-t* f-t*)])
         (context-case ctxt
           [(app/let) #;FIXME ;also for apply / call-with-values ?
            (when (fx= (length cl*) 1)
              (set-box! ret (unbox (car r*)))
              (predicates-merge! types (car t*) (car x**))
              (predicates-merge! t-types (car t-t*) (car x**))
              (predicates-merge! f-types (car f-t*) (car x**)))]
            [else (void)])
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f)) e* r* t*)]
              [e0 (nanopass-case (Lsrc Expr) e0
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)) ;move this part to case-lambda
                     (guard (fx= interface (length x*)))
                     (for-each (lambda (t) (predicates-merge! types t '())) t*)
                     (let ([subtypes (predicates-copy types)])
                       (for-each (lambda (x r) (predicates-add! subtypes x (unbox r))) x* r*)
                       (let* ([t-subtypes (predicates-copy subtypes)]
                              [f-subtypes (predicates-copy subtypes)]
                              [e0 (cptypes e0 'app/let ret subtypes t-subtypes f-subtypes)])  #;FIXME
                         (predicates-merge! types subtypes x*)
                         (predicates-merge! t-types t-subtypes x*)
                         (predicates-merge! f-types f-subtypes x*)
                         e0))]
                    [(case-lambda ,preinfo ,cl* ...)
                     (for-each (lambda (t) (predicates-merge! types t '())) t*)
                     (cptypes e0 'app/let ret types t-types f-types)]  #;FIXME
                    [else
                      (let* ([r0 (box #f)]
                             [t0 (predicates-copy types)]
                             [e0 (cptypes e0 'value r0 t0 #f #f)]) #;FIXME
                        (for-each (lambda (t) (predicates-merge! types t '())) t*)
                        (predicates-merge! types t0 '())
                        e0)])])
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ([,x* ,e*] ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f)) e* r* t*)])
         (for-each (lambda (t) (predicates-merge! types t x*)) t*)
         (let ([subtypes (predicates-copy types)])
           (for-each (lambda (x r) (predicates-add! subtypes x (unbox r))) x* r*)
           (let* ([t-subtypes (predicates-copy subtypes)]
                  [f-subtypes (predicates-copy subtypes)]
                  [body (cptypes body ctxt ret subtypes t-subtypes f-subtypes)])
             (predicates-merge! types subtypes x*)
             (predicates-merge! t-types t-subtypes x*)
             (predicates-merge! f-types f-subtypes x*)
             `(letrec ([,x* ,e*] ...) ,body))))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([subtypes (predicates-copy types)]
              [r* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (x e r)
                         (let ([e (cptypes e 'value r subtypes #f #f)])
                           (predicates-add! subtypes x (unbox r))
                           e))
                    x* e* r*)]
              [t-subtypes (predicates-copy subtypes)]
              [f-subtypes (predicates-copy subtypes)]
              [body (cptypes body ctxt ret subtypes t-subtypes f-subtypes)])
         (predicates-merge! types subtypes x*)
         (predicates-merge! t-types t-subtypes x*)
         (predicates-merge! f-types f-subtypes x*)
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr ir]
      [(foreign ,conv ,name ,[cptypes : e 'value (box #f) types #f #f -> e] (,arg-type* ...) ,result-type)
       `(foreign ,conv ,name ,e (,arg-type* ...) ,result-type)]
      [(fcallable ,conv ,[cptypes : e 'value (box #f) types #f #f -> e] (,arg-type* ...) ,result-type)
       `(fcallable ,conv ,e (,arg-type* ...) ,result-type)]
      [(record ,rtd ,rtd-expr ,e* ...)
       (let* ([t-rtd-expr (predicates-copy types)]
              [rtd-expr (cptypes rtd-expr 'value (box #f) t-rtd-expr #f #f)]
              [t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e 'value (box #f) t #f #f)) e* t*)])
         (predicates-merge! types t-rtd-expr '())
         (for-each (lambda (t) (predicates-merge! types t '())) t*)
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e 'value (box #f) types #f #f -> e])
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can be reordered?
       (let* ([t1 (predicates-copy types)]
              [t2 (predicates-copy types)]
              [e1 (cptypes e1 'value (box #f) t1 #f #f)]
              [e2 (cptypes e2 'value (box #f) t2 #f #f)])
       (predicates-merge! types t1 '())
       (predicates-merge! types t2 '())
       `(record-set! ,rtd ,type ,index ,e1 ,e2))]
      [(record-type ,rtd ,[cptypes : e 'value (box #f) types  #f #f -> e])
       `(record-type ,rtd ,e)]
      [(record-cd ,rcd ,rtd-expr ,[cptypes : e 'value (box #f) types #f #f -> e])
       `(record-cd ,rcd ,rtd-expr ,e)]
      [(immutable-list (,e* ...) ,e)
       (let* ([t* (map (lambda (e) (predicates-copy types)) e*)]
              [e* (map (lambda (e t) (cptypes e 'value (box #f) t #f #f)) e* t*)]
              [e (cptypes e 'value ret types #f #f)]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      [(moi) ir]
      [(pariah) ir]
      [(cte-optimization-loc ,box0 ,[cptypes : e 'value (box #f) types  #f #f -> e]) ;don't shadow box
       `(cte-optimization-loc ,box0 ,e)]
      [(cpvalid-defer ,e) (sorry! who "cpvalid leaked a cpvalid-defer form ~s" ir)]
      [(profile ,src) ir]
      [else ($oops who "unrecognized record ~s" ir)]))

(lambda (x)
  (cptypes x 'value (box #f) (predicates-new) #f #f))
))
