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
   types: a "predicates" record. Actually just a box with an assoc, but let's
          pretend it's something fancy and immutable, and manipulate it using
          only the API.
          It has the associations of prelex to types that were discovered before.
          (box ((x . 'pair?) (y . 'vector) (z . `(quote 0))))
   ret [out]: a box to return the type of the result of the expression
   n-types [out]: a box to return the types to be used in the next expression.
                  Add the new discovered predicates to types.
                  If left blank (box #f) it will be automaticaly filled with a
                  copy of types.
   t-types [out]: a box to return the types to be used in case the expression
                  is not #t, to be used in the "then" branch of an if.
                  Fill only when you fill ret.
                  If left blank (box #f) it will be automaticaly filled with a
                  copy of n-types (that may be an automatic copy of types).
   f-types [out]: idem for the "else" branch. (if x (something) (here x is #f))


 - predicate: (each one, not the record)
              They may be:
              * a symbol to indicate the type, like 'vector? 'pair? 'number?
                (there are a few fake values, in particular 'bottom? is used to
                 signal that there is an error)
              * a nanopass-quoted value that is okay-to-copy?, like
                `(quote 0) `(quote 5) `(quote #t) `(quote '())
                (this doesn't includes `(quote <record-type-descriptor?>))
              * a [normal] list ($record? <rtd>) to signal that it's a record
                of type <rtd>
              * TODO: add something to indicate that x is a procedure to
                      create/setter/getter/predicate of a record of that type
              * TODO: add primitives, probably the nanopass version of pr
              * TODO: add procedure? and perhaps some minimal signature for them


 - most of the time I'm using eq? and eqv? as if they were equivalent.
   this is not a good idea.
 - most FIXME are not bugs but sites were the code can be improved.
 - most CHECK are parts where I'm not sure that it is correct.

|#

[define $cptypes
[let ()
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

  (define (predicates-add types x type)
    (cond
      [(and types
            x
            type
            (not (eq? type 'ptr?))
            (not (prelex-was-assigned x))
            (not (assoc x (unbox types))))
       (box (cons (cons x type) (unbox types)))]
      [else types]))

  (define (predicates-merge types from skipped)
    (cond
      [(and types from)
       (let ([base (unbox types)]) ;try to avoid common part
         (let loop ([types types] [from (unbox from)])
           (cond
             [(and (not (null? from))
                   (not (eq? from base)))
              (let ([a (car from)])
                (cond
                  [(member (car a) skipped)
                   (loop types (cdr from))]
                  [else
                   (loop (predicates-add types (car a) (cdr a)) (cdr from))]))]
              [else types])))]
      [else types]))

  (define (predicates-lookup types x)
    (and types
         (not (prelex-was-assigned x))
         (let ([a (assoc x (unbox types))])
           (and a (cdr a)))))

  (define (predicates-add/ref types r pred)
    (nanopass-case (Lsrc Expr) r
      [(ref ,maybe-src ,x)
       (predicates-add types x pred)]
      [else types]))

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
          (record-type-descriptor? obj)))) ;removed in datum->predicate

  (define (datum->predicate d ir)
    (cond
      [(#3%$record? d) '$record?] ;check first to avoid doube representation of rtd
      [(okay-to-copy? d) ir]
      [(pair? d) 'pair?]
      [(box? d) 'box?]
      [(vector? d) 'vector?]
      [(string? d) 'string?]
      [(bytevector? d) 'bytevector?]
      [(fxvector? d) 'fxvector?]
      [else #f]))

  (define (rtd->record-predicate rtd)
    (cond
      [(record-type-descriptor? rtd)
       (list '$record? rtd)]
      [(Lsrc? rtd)
       (nanopass-case (Lsrc Expr) rtd
         [(quote ,d)
          (cond
            [(record-type-descriptor? d)
             (list '$record? d)]
            [else '$record?])]
         [(record-type ,rtd ,e)
          (cond
            [(record-type-descriptor? rtd)
             (list '$record? rtd)]
            [else '$record?])]
         [else '$record?])]
      [else '$record?]))

  (define (primref-name->predicate name extend?)
    (case name
      [(pair? box?
        $record?
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
      #;[$black-hole? "'#7=#7#"-rec] ;???
      #;[$unbound-object? unbound-rec] ;???
      #;[vector-empty? empty-vector-rec]
      #;[string-empty? empty-string-rec]
      #;[bytevector-empty? empty-bytevector-rec]
      #;[fxvector-empty? empty-fxvector-rec]
      [else (and extend? ;---------------------------------------------------
            (case name
              [(record?) '$record?]
              [(list?) 'null-or-pair?] ;fake-predicate
              [(bit? length? ufixnum? pfixnum?) 'fixnum?]
              [(sint? uint? exact-integer?) 'integer?] ;perhaps use exact-integer?
              [(uinteger?) 'integer?]
              [(flonum? rational? real? cflonum?) 'number?]
              [else #f]))]))

  (define (primref->predicate pr extend?)
    (primref-name->predicate (primref-name pr) extend?))

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
             (and (pair? x) (pair? (cdr x)) (eq? (car x) '$record?)
                  (pair? y) (pair? (cdr y)) (eq? (car y) '$record?)
                  (let loop ([x (cadr x)] [y (cadr y)])
                    (or (eqv? x y)
                        (let ([xp (record-type-parent x)])
                          (and xp (loop xp y))))))
             (eq? x 'bottom?)
             (cond
               [(eq? y 'null-or-pair?) (or (check-constant-is? x null?)
                                           (eq? x 'pair?))]
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
               [(eq? y '$record?) (or (check-constant-is? x #3%$record?)
                                      (and (pair? x) (eq? (car x) '$record?)))]
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
              (let ([results (map signature->result-predicate signatures)])
                (ormap (lambda (one-result)
                         (and (andmap (lambda (result) ;TODO: Get a better union of multiple results
                                        (check-predicate-implies? result one-result))
                                      results)
                              one-result))
                       results))))]))

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
           (let ([vals (map (lambda (signature)
                              (signature->argument-predicate signature pos))
                            signatures)])
             (ormap (lambda (one-val)
                      (and (andmap (lambda (val) ;TODO: Get a better union of multiple vals
                                     (check-predicate-implies? val one-val))
                                   vals)
                           one-val))
                    vals)))))

  [define-pass cptypes/raw : Lsrc (ir ctxt types ret n-types t-types f-types) -> Lsrc ()
    [Expr : Expr (ir) -> Expr ()
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
               (set-box! f-types (predicates-add/ref types ir false-rec))
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
              [n-types1 (box #f)]
              [e1 (cptypes e1 'effect types r1 n-types1 (box #f) (box #f))])
         (cond
           [(check-predicate-implies? (unbox r1) 'bottom?)
            (set-box! ret (unbox r1))
            e1]
           [else
            (let ([e2 (cptypes e2 ctxt (unbox n-types1) ret n-types t-types f-types)])
              (make-seq ctxt e1 e2))]))]
      [(if ,e1 ,e2 ,e3)
       (let* ([r1 (box #f)]
              [n-types1 (box #f)]
              [t-types1 (box #f)]
              [f-types1 (box #f)]
              [e1 (cptypes e1 'test types r1 n-types1 t-types1 f-types1)])
         (cond
           [(check-predicate-implies? (unbox r1) 'bottom?) ;check bottom first
            (set! ret (unbox r1))
            e1]
           [(check-predicate-implies-not? (unbox r1) false-rec)
            (let ([e2 (cptypes e2 ctxt (unbox t-types1) ret n-types t-types f-types)])
              (make-seq ctxt e1 e2))]
           [(check-predicate-implies? (unbox r1) false-rec)
            (let ([e3 (cptypes e3 ctxt (unbox f-types1) ret n-types t-types f-types)])
              (make-seq ctxt e1 e3))]
           [else
            (let* ([r2 (box #f)]
                   [n-types2 (box #f)]
                   [t-types2 (box #f)]
                   [f-types2 (box #f)]
                   [e2 (cptypes e2 ctxt (unbox t-types1) r2 n-types2 t-types2 f-types2)]
                   [r3 (box #f)]
                   [n-types3 (box #f)]
                   [t-types3 (box #f)]
                   [f-types3 (box #f)]
                   [e3 (cptypes e3 ctxt (unbox f-types1) r3 n-types3 t-types3 f-types3)])
              (set-box! n-types (unbox n-types1))
              (set-box! t-types (unbox n-types1))
              (set-box! f-types (unbox n-types1))
              (cond
                [(check-predicate-implies? (unbox r2) 'bottom?) ;check bottom first
                 (set-box! t-types (unbox t-types3))
                 (set-box! f-types (unbox f-types3))
                 (set-box! ret (unbox r3))
                 (set-box! n-types (unbox n-types3))]
                [(check-predicate-implies-not? (unbox r2) false-rec)
                 (set-box! f-types (predicates-merge (unbox f-types) (unbox f-types3) '()))]
                [(check-predicate-implies? (unbox r2) false-rec)
                 (set-box! t-types (predicates-merge (unbox t-types) (unbox t-types3) '()))])
              (cond
                [(check-predicate-implies? (unbox r3) 'bottom?) ;check bottom first
                 (set-box! t-types (unbox t-types2))
                 (set-box! f-types (unbox f-types2))
                 (set-box! ret (unbox r2))
                 (set-box! n-types (unbox n-types2))]
                [(check-predicate-implies-not? (unbox r3) false-rec)
                 (set-box! f-types (predicates-merge (unbox f-types) (unbox f-types2) '()))]
                [(check-predicate-implies? (unbox r3) false-rec)
                 (set-box! t-types (predicates-merge (unbox t-types) (unbox t-types2) '()))])
              (cond #;FIXME
                [(check-predicate-implies? (unbox r2) (unbox r3))
                 (set-box! ret (unbox r3))]
                [(check-predicate-implies? (unbox r3) (unbox r2))
                 (set-box! ret (unbox r2))]
                [else (void)])
              `(if ,e1 ,e2 ,e3))]))]
      [(set! ,maybe-src ,x ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e])
       (set-box! ret void-rec)
       `(set! ,maybe-src ,x ,e)]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [n-t* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r n-t) (cptypes e 'value types r n-t (box #f) (box #f)))
                       e* r* n-t*)]
              [ir `(call ,preinfo ,pr ,e* ...)])
         (set-box! n-types types)
         (for-each (lambda (n-t) (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t) '()))) n-t*)
         (set-box! ret (primref->result-predicate pr))
         (for-each (lambda (e n)
                     (let ([pred (primref->argument-predicate pr n)])
                       (set-box! n-types (predicates-add/ref (unbox n-types) e pred))))
                   e* (enumerate e*))
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
                 (set-box! t-types (or (unbox n-types) types))
                 (set-box! t-types (predicates-add/ref (unbox t-types) e1 (unbox r2)))
                 (set-box! t-types (predicates-add/ref (unbox t-types) e2 (unbox r1)))
                 ir]))]
           [(and (fx= (length e*) 1)
                 (primref->predicate pr #f))
            (let ([pred (primref->predicate pr #f)]
                  [var (unbox (car r*))])
              (cond
                [(check-predicate-implies? var pred)
                 (set-box! ret true-rec)
                 (make-seq ctxt (car e*) true-rec)]
                [(check-predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else
                 (set-box! t-types (predicates-add/ref (or (unbox n-types) types) (car e*) pred))
                 ir]))]
           [(and (fx= (length e*) 1)
                 (primref->predicate pr #t))
            (let ([pred (primref->predicate pr #t)]
                  [var (unbox (car r*))])
              (cond
                ; no (pred? <ext-pred?>) => #t
                [(check-predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else
                 (set-box! t-types (predicates-add/ref (or (unbox n-types) types) (car e*) pred))
                 ir]))]
           [(and (fx>= (length e*) 1)
                 (eq? (primref-name pr) 'record))
            (set-box! ret (rtd->record-predicate (car e*)))
            ir]
           [(and (fx= (length e*) 2)
                 (eq? (primref-name pr) 'record?))
            (let ([pred (rtd->record-predicate (cadr e*))]
                  [var (unbox (car r*))])
              #;(when (eq? pred '$record?)
                   (newline)
                   (newline)
                   (display (cadr e*))
                   (newline)
                   (newline))
              (cond
                [(check-predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) false-rec)]
                [(and (not (eq? pred '$record?)) ; assume that the only extension is '$record?
                      (check-predicate-implies? var pred))
                 (set-box! ret true-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) true-rec)]
                [else
                 (set-box! t-types (predicates-add/ref (or (unbox n-types) types) (car e*) pred))
                 ir]))]
           [(and (fx= (length e*) 2)
                 (eq? (primref-name pr) '$sealed-record?))
            (let ([pred (rtd->record-predicate (cadr e*))]
                  [var (unbox (car r*))])
              (cond
                [(check-predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) false-rec)]
                [(and (not (eq? pred '$record?)) ; assume that the only extension is '$record?
                      (pair? pred) (pair? (cdr pred)) (eq? (car pred) '$record?) ;just in case
                      (record-type-descriptor? (cadr pred))
                      (record-type-sealed? (cadr pred))
                      (check-predicate-implies? var pred))
                 (set-box! ret true-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) true-rec)]
                [else
                 (set-box! t-types (predicates-add/ref (or (unbox n-types) types) (car e*) pred))
                 ir]))]
           [else
            ir]))]
      [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
       (let* ([r (box #f)]
              [n-t (box #f)]
              [t-t (box #f)]
              [f-t (box #f)]
              [body (cptypes body 'value types r n-t t-t f-t)]) #;FIXME
         (context-case ctxt
           [(app/let) #;FIXME ;also for apply / call-with-values ?
              (set-box! ret (unbox r))
              (set-box! n-types (unbox n-t))
              (set-box! t-types (unbox t-t))
              (set-box! f-types (unbox f-t))]
            [else (void)])
         `(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)))]
      [(case-lambda ,preinfo ,cl* ...)
       (let* ([cl* (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body 'value types (box #f) (box #f) (box #f) (box #f))]) #;FIXME
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                        cl*)])
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [n-t* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r n-t) (cptypes e 'value types r n-t (box #f) (box #f))) e* r* n-t*)]
              [e0 (nanopass-case (Lsrc Expr) e0
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)) ;move this part to case-lambda
                     (guard (fx= interface (length x*)))
                     (set-box! n-types types)
                     (for-each (lambda (n-t) (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t) '()))) n-t*)
                     (let ([subtypes (box (unbox n-types))])
                       (for-each (lambda (x r) (set-box! subtypes (predicates-add (unbox subtypes) x (unbox r)))) x* r*)
                       (let* ([n-subtypes (box #f)]
                              [t-subtypes (box #f)]
                              [f-subtypes (box #f)]
                              [e0 (cptypes e0 'app/let (unbox subtypes) ret n-subtypes t-subtypes f-subtypes)]) #;FIXME
                         (set-box! n-types (predicates-merge (unbox n-types) (unbox n-subtypes) x*))
                         (set-box! t-types (predicates-merge (unbox n-types) (unbox t-subtypes) x*))
                         (set-box! f-types (predicates-merge (unbox n-types) (unbox f-subtypes) x*))
                         e0))]
                    [(case-lambda ,preinfo ,cl* ...)
                     (set-box! n-types types)
                     (for-each (lambda (n-t) (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t) '()))) n-t*)
                     (cptypes e0 'value (unbox n-types) (box #f) (box #f) (box #f) (box #f))]  #;FIXME
                    [else
                      (let* ([r0 (box #f)]
                             [n-t0 (box #f)]
                             [e0 (cptypes e0 'value types r0 n-t0 (box #f) (box #f))]) #;FIXME
                        (set-box! n-types (unbox n-t0))
                        (for-each (lambda (n-t) (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t) '()))) n-t*)
                        e0)])])
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ((,x* ,e*) ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [n-t* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e r n-t) (cptypes e 'value types r n-t (box #f) (box #f))) e* r* n-t*)]
              [subtypes (box types)])
         (for-each (lambda (n-t) (set-box! subtypes (predicates-merge (unbox subtypes) (unbox n-t) '()))) n-t*)
         (for-each (lambda (x r) (set-box! subtypes (predicates-add (unbox subtypes) x (unbox r)))) x* r*)
         (let* ([n-subtypes (box #f)]
                [t-subtypes (box #f)]
                [f-subtypes (box #f)]
                #;[body (cptypes body ctxt (unbox subtypes) ret n-subtypes t-subtypes f-subtypes)])
           (set-box! n-types (predicates-merge types (unbox n-subtypes) x*))
           (set-box! t-types (predicates-merge (unbox n-types) (unbox t-subtypes) x*))
           (set-box! f-types (predicates-merge (unbox n-types) (unbox f-subtypes) x*))
           `(letrec ((,x* ,e*) ...) ,body)))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([subtypes (box types)]
              [e* (let loop ([x* x*] [e* e*] [rev-e* '()])
                    (if (null? x*)
                        (reverse rev-e*)
                        (let* ([n-subtypes (box #f)]
                               [r (box #f)]
                               [e (cptypes (car e*) 'value (unbox subtypes) r n-subtypes (box #f) (box #f))])
                           (set-box! subtypes (predicates-add (unbox n-subtypes) (car x*) (unbox r)))
                           (loop (cdr x*) (cdr e*) (cons e rev-e*)))))]
              [n-subtypes (box #f)]
              [t-subtypes (box #f)]
              [f-subtypes (box #f)]
              [body (cptypes body ctxt (unbox subtypes) ret n-subtypes t-subtypes f-subtypes)])
         (set-box! n-types (predicates-merge types (unbox n-subtypes) x*))
         (set-box! t-types (predicates-merge (unbox n-types) (unbox t-subtypes) x*))
         (set-box! f-types (predicates-merge (unbox n-types) (unbox f-subtypes) x*))
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr ir]
      [(foreign ,conv ,name ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e] (,arg-type* ...) ,result-type)
       `(foreign ,conv ,name ,e (,arg-type* ...) ,result-type)]
      [(fcallable ,conv ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e] (,arg-type* ...) ,result-type)
       `(fcallable ,conv ,e (,arg-type* ...) ,result-type)]
      [(record ,rtd ,rtd-expr ,e* ...)
       (let* ([n-t-rtd-expr (box #f)]
              [rtd-expr (cptypes rtd-expr 'value types (box #f) n-t-rtd-expr (box #f) (box #f))]
              [n-t* (map (lambda (e) (box #f)) e*)]
              [e* (map (lambda (e n-t) (cptypes e 'value types (box #f) n-t (box #f) (box #f))) e* n-t*)])
         (set-box! n-types (unbox n-t-rtd-expr))
         (for-each (lambda (n-t) (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t) '()))) n-t*)
         (set-box! ret (rtd->record-predicate rtd))
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e])
       (set-box! n-types (predicates-add/ref types e (rtd->record-predicate rtd)))
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can be reordered?
       (let* ([n-t1 (box #f)]
              [n-t2 (box #f)]
              [e1 (cptypes e1 'value types (box #f) n-t1 (box #f) (box #f))]
              [e2 (cptypes e2 'value types (box #f) n-t2 (box #f) (box #f))])
         (set-box! n-types types)
         (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t1) '()))
         (set-box! n-types (predicates-merge (unbox n-types) (unbox n-t2) '()))
         (set-box! n-types (predicates-add/ref (unbox n-types) e1 (rtd->record-predicate rtd)))
         `(record-set! ,rtd ,type ,index ,e1 ,e2))]
      [(record-type ,rtd ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e])
       `(record-type ,rtd ,e)]
      [(record-cd ,rcd ,rtd-expr ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e])
       `(record-cd ,rcd ,rtd-expr ,e)]
      [(immutable-list (,e* ...) ,e)
       (let* ([e* (map (lambda (e) (cptypes e 'value types (box #f) (box #f) (box #f) (box #f))) e*)]
              [e (cptypes e 'value types ret n-types (box #f) (box #f))]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      [(moi) ir]
      [(pariah) ir]
      [(cte-optimization-loc ,box0 ,[cptypes : e 'value types (box #f) n-types (box #f) (box #f) -> e]) ;don't shadow box
       `(cte-optimization-loc ,box0 ,e)]
      [(cpvalid-defer ,e) (sorry! who "cpvalid leaked a cpvalid-defer form ~s" ir)]
      [(profile ,src) ir]
      #;[else ir]
      [else ($oops who "unrecognized record ~s" ir)]]]

  (define (cptypes ir ctxt types ret n-types t-types f-types)
    (let ([ir (cptypes/raw ir ctxt types ret n-types t-types f-types)])
      (unless (unbox n-types)
        (set-box! n-types types))
      (unless (unbox t-types)
        (set-box! t-types (unbox n-types)))
      (unless (unbox f-types)
        (set-box! f-types (unbox n-types)))
      ir))

  (lambda (x)
    (cptypes x 'value (predicates-new) (box #f) (box #f) (box #f) (box #f)))
]]
