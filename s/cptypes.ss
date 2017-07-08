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

   ctxt: 'effect 'test 'value
   ret [out]: a box to return the type of the result of the expression
   types [in/out]: a box with a "pred-env" record. It's record with a hamt (for
                   fast lookup) and anssocistion list (to get the last additions).
                   Use it only with the API so it's posible to cange the
                   implementation later. The pred-env is immutable.
                   The hamt/associations of prelex to discovered types.
                   ((x . 'pair?) (y . 'vector?) (z . `(quote 0)))
   t-types [out]: a box to return the types to be used in case the expression
                  is not #f, to be used in the "then" branch of an if.
                  Fill only when you fill ret.
                  If left blank (box #f) it will be automaticaly filled with a
                  copy of types.
                  It may also be #f (not a box) when the calling function will
                  ignore it.
   f-types [out]: idem for the "else" branch. (if x (something) (here x is #f))


 - predicate: They may be:
              * a symbol to indicate the type, like 'vector? 'pair? 'number?
                (there are a few fake values, in particular 'bottom? is used to
                 signal that there is an error)
              * a nanopass-quoted value that is okay-to-copy?, like
                `(quote 0) `(quote 5) `(quote #t) `(quote '())
                (this doesn't includes `(quote <record-type-descriptor?>))
              * a [normal] list ($record? <rtd>) to signal that it's a record
                of type <rtd>
              * TODO?: add something to indicate that x is a procedure to
                       create/setter/getter/predicate of a record of that type

 - Primitives are marked as procedures, without distinction.
 - Most of the time I'm using eq? and eqv? as if they were equivalent.
   I assume that the differences are hidden by unespecified behaivior.

|#


(define $cptypes
(let ()
  (import (nanopass))
  (include "base-lang.ss")

  (module (hamt-empty hamt-ref hamt-set)
    (include "hamt.ss")
    (define hamt-empty $hamt-empty)
    (define (hamt-ref hash key default) ($hamt-ref hash key equal-hash equal? default))
    (define (hamt-set hash key val) ($hamt-set hash key equal-hash equal? val))
  )

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

    (define (simple? e) ; Simplified version copied from cp0. TODO: copy the rest.
      (nanopass-case (Lsrc Expr) e
        [(quote ,d) #t]
        [(ref ,maybe-src ,x) #t]
        [(case-lambda ,preinfo ,cl* ...) #t]
        [,pr #t]
        [(moi) #t]
        [else #f]
        #;[else ($oops who "unrecognized record ~s" e)]))

    ; TODO: Remove discardable operations in e1. (vector (f) (g)) => (begin (f) (g))
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

    #;(define make-seq* ; requires at least one operand
        (lambda (ctxt e*)
          (if (null? (cdr e*))
              (car e*)
              (make-seq ctxt (car e*) (make-seq* ctxt (cdr e*))))))
  )

  (module (pred-env-empty pred-env-add pred-env-merge pred-env-lookup)

    (define-record-type pred-env
      (nongenerative)
      (opaque #t)
      (fields hamt assoc depth))
    ; depth is the length of the assoc. It may be bigger than the count of the
    ; hamt in case a predicate was "replaced" with a more specific one. 

    (define pred-env-empty
      (make-pred-env (hamt-empty) '() 0))

    (define (pred-env-add/raw types x pred)
      (make-pred-env (hamt-set (pred-env-hamt types) x pred)
                     (cons (cons x pred) (pred-env-assoc types))
                     (fx+ 1 (pred-env-depth types))))

    (define (pred-env-add types x pred)
      (cond
        [(and #;types
              x
              pred
              (not (eq? pred 'ptr?)) ; filter 'ptr? to reduce the size
              (not (prelex-was-assigned x)))
         (let ([old (hamt-ref (pred-env-hamt types) x #f)])
           (cond
             [(not old)
              (pred-env-add/raw types x pred)]
             [(predicate-implies? old pred)
              types]
             [(or (predicate-implies-not? old pred)
                  (predicate-implies-not? pred old))
              (pred-env-add/raw types x 'bottom)]
             [else
              (pred-env-add/raw types x pred)]))]
        [else types]))

  (define (pred-env-merge/raw types base n from skipped)
    (let loop ([types types]
               [base base]
               [n n]
               [from from])
      (cond
        [(and (not (null? from))
              (not (eq? from base)))
         (let* ([a (car from)]
                [types (cond
                         [(member (car a) skipped)
                          types]
                         [else
                          (pred-env-add types (car a) (cdr a))])]
                [base (and base
                           (if (fx> n 0)
                              base
                              (cdr base)))])
           (loop types base (fx- n 1) (cdr from)))]
        [else types])))

  (define (pred-env-merge types from skipped)
    ; When possible we will trim the assoc in types to make it of the same
    ; length of the assoc in from. But we will avoid this if it is too long. 
    (cond
      #;[(not from)
       types]
      #;[(not types)
       (pred-env-merge/raw pred-env-empty #f 0 (pred-env-assoc from) skipped)]
      [(> (pred-env-depth types) (fx* (pred-env-depth from) 5))
       (pred-env-merge/raw types #f 0 (pred-env-assoc from) skipped)]
      [(> (pred-env-depth types) (pred-env-depth from))
       (pred-env-merge/raw types 
                           (list-tail (pred-env-assoc types)
                                      (fx- (pred-env-depth types) (pred-env-depth from)))
                            0
                           (pred-env-assoc from)
                           skipped)]
      [else 
       (pred-env-merge/raw types
                           (pred-env-assoc types)
                           (fx- (pred-env-depth from) (pred-env-depth types))
                           (pred-env-assoc from)
                           skipped)]))

    (define (pred-env-lookup types x)
      (and types
           (not (prelex-was-assigned x))
           (hamt-ref (pred-env-hamt types) x #f)))
  )

  (define (pred-env-add/ref types r pred)
    (nanopass-case (Lsrc Expr) r
      [(ref ,maybe-src ,x)
       (pred-env-add types x pred)]
      [else types]))

  ;copied from cp0.ss
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
      [(and (integer? d) (exact? d)) 'exact-integer?]
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
        fixnum? #;exact-integer? flonum? real? number?
        vector? string? bytevector? fxvector?
        gensym? symbol?
        char?
        bottom? ptr?  ;pseudo-predicates
        boolean?
        procedure?)
        name]
      [void? void-rec] ;fake-predicate
      #;[true-object? true-rec]
      [not false-rec]
      #;[not? false-rec]
      [null? null-rec]
      [eof-object? eof-rec]
      [bwp-object? bwp-rec]
      #;[$black-hole? black-hole-rec] ;???
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
                   [(sint? uint? exact-integer?) 'exact-integer?] ;fake-predicate
                   [(uinteger? rational?) 'real?]
                   [(cflonum?) 'number?]
                   [else #f]))]))

  ; nqm: no question mark
  ; this is duplicated code, but it's useful to avoid the allocation 
  ; of the temporal strings to transform: vector -> vector?
  (define (primref-name/nqm->predicate name extend?)
    (case name
      [pair 'pair?]
      [box 'box?]
      [$record '$record?]
      [fixnum 'fixnum?]
      [flonum 'flonum?]
      [real 'real?]
      [number 'number?]
      [vector 'vector?]
      [string 'string?]
      [bytevector 'bytevector?]
      [fxvector 'fxvector?]
      [gensym 'gensym?]
      [symbol 'symbol?]
      [char 'char?]
      [bottom 'bottom?];pseudo-predicates
      [ptr 'ptr?];pseudo-predicates
      [boolean 'boolean?]
      [procedure 'procedure?]
      [void void-rec] ;fake-predicate
      #;[not false-rec]
      [null null-rec]
      [eof-object eof-rec]
      [bwp-object bwp-rec]
      [else (and extend? ;---------------------------------------------------
                 (case name
                   [(record) '$record?]
                   [(list) 'null-or-pair?] ;fake-predicate
                   [(bit length ufixnum pfixnum) 'fixnum?]
                   [(sint uint exact-integer) 'exact-integer?] ;fake-predicate
                   [(uinteger rational) 'real?]
                   [(cflonum) 'number?]
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
  (define (predicate-implies? x y)
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
             (case y
               [(null-or-pair?) (or (check-constant-is? x null?)
                                    (eq? x 'pair?))]
               #;[(pair?) (check-constant-is? x pair?)]
               #;[(box?) (check-constant-is? x box?)]
               [(fixnum?) (check-constant-is? x target-fixnum?)]
               [(exact-integer?)
                (or (eq? x 'fixnum?)
                    (check-constant-is? x (lambda (x) (and (integer? x)
                                                           (exact? x)))))]
               [(flonum?) (check-constant-is? x flonum?)]
               [(real?) (or (eq? x 'fixnum?)
                            (eq? x 'exact-integer?)
                            (eq? x 'flonum?)
                            (check-constant-is? x real?))]
               [(number?) (or (eq? x 'fixnum?)
                              (eq? x 'exact-integer?)
                              (eq? x 'flonum?)
                              (eq? x 'real?)
                              (check-constant-is? x number?))]
               [(vector?) (check-constant-is? x vector?)]
               [(string?) (check-constant-is? x string?)]
               [(bytevector?) (check-constant-is? x bytevector?)]
               [(fxvector?) (check-constant-is? x fxvector?)]
               [(gensym?) (check-constant-is? x gensym?)]
               [(symbol?) (or (eq? x 'gensym?)
                              (check-constant-is? x symbol?))]
               [(char?) (check-constant-is? x char?)]
               [(boolean?) (or (check-constant-is? x not)
                               (check-constant-is? x (lambda (x) (eq? x #t))))]
               [($record?) (or (check-constant-is? x #3%$record?)
                               (and (pair? x) (eq? (car x) '$record?)))]
               [(ptr?) #t]
               [else #f]))))

  (define (predicate-implies-not? x y)
    ; for now this is enough
    (and x
         y
         (not (predicate-implies? x y))
         (not (predicate-implies? y x))))

  #;(define (symbol-append . x)
      (string->symbol
       (apply string-append (map symbol->string x))))

  (define (signature->result-predicate signature)
    (let ([results (cdr signature)])
      (and (fx= (length results) 1)
           (let ([result (car results)])
             (cond
               [(symbol? result)
                (primref-name/nqm->predicate result #t)]
               [(pair? result)
                (primref-name->predicate 'pair? #t)]
               [else
                #f])))))

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
                                        (predicate-implies? result one-result))
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
            (primref-name/nqm->predicate (list-ref arguments pos) #t)]
           [else
            (primref-name/nqm->predicate (list-ref arguments (- (length arguments) 2)) #t)])]
         [dots #f] ; TODO: Extend to handle this case, perhaps knowing the argument count.
         [else
          (cond
            [(< pos (length arguments))
             (let ([argument (list-ref arguments pos)])
               (if (pair? argument)
                   (primref-name->predicate 'pair? #t)
                   (primref-name/nqm->predicate argument #t)))]
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
                                     (predicate-implies? val one-val))
                                   vals)
                           one-val))
                    vals)))))

  [define-pass cptypes/raw : Lsrc (ir ctxt ret types t-types f-types) -> Lsrc ()
    [Expr : Expr (ir) -> Expr ()
      [(quote ,d)
       (set-box! ret (datum->predicate d ir))
       ir]
      [(ref ,maybe-src ,x)
       (case ctxt
         [(test)
          (let ([t (pred-env-lookup (unbox types) x)])
            (cond
              [(predicate-implies-not? t false-rec)
               (set-box! ret true-rec)
               true-rec]
              [(predicate-implies? t false-rec)
               (set-box! ret false-rec)
                false-rec]
              [else
               (set-box! ret t)
               (set-box! f-types (pred-env-add/ref (unbox types) ir false-rec))
               ir]))]
         [else
           (let ([t (pred-env-lookup (unbox types) x)])
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
           [(predicate-implies? (unbox r1) 'bottom?)
            (set-box! ret (unbox r1))
            e1]
           [else
            (let ([e2 (cptypes e2 ctxt ret types t-types f-types)])
              (make-seq ctxt e1 e2))]))]
      [(if ,e1 ,e2 ,e3)
       (let* ([r1 (box #f)]
              [t-types1 (box #f)]
              [f-types1 (box #f)]
              [e1 (cptypes e1 'test r1 types t-types1 f-types1)])
         (cond
           [(predicate-implies? (unbox r1) 'bottom?) ;check bottom first
            (set! ret (unbox r1))
            e1]
           [(predicate-implies-not? (unbox r1) false-rec)
            (let ([e2 (cptypes e2 ctxt ret types t-types f-types)])
              (make-seq ctxt e1 e2))]
           [(predicate-implies? (unbox r1) false-rec)
            (let ([e3 (cptypes e3 ctxt ret types t-types f-types)])
              (make-seq ctxt e1 e3))]
           [else
            (let* ([r2 (box #f)]
                   [t-types2 (and t-types (box #f))]
                   [f-types2 (and f-types (box #f))]
                   [e2 (cptypes e2 ctxt r2 t-types1 t-types2 f-types2)]
                   [r3 (box #f)]
                   [types3 (box #f)]
                   [t-types3 (and t-types (box #f))]
                   [f-types3 (and f-types (box #f))]
                   [e3 (cptypes e3 ctxt r3 f-types1 t-types3 f-types3)])
              (when t-types
                (set-box! t-types (unbox types)))
              (when f-types
               (set-box! f-types (unbox types)))
              (cond
                [(predicate-implies? (unbox r2) 'bottom?) ;check bottom first
                 (when t-types
                   (set-box! t-types (unbox t-types3)))
                 (when f-types
                   (set-box! f-types (unbox f-types3)))
                 (set-box! ret (unbox r3))
                 (set-box! types (unbox f-types1))]
                [(predicate-implies-not? (unbox r2) false-rec)
                 (when f-types
                   (set-box! f-types (pred-env-merge (unbox f-types) (unbox f-types3) '())))]
                [(predicate-implies? (unbox r2) false-rec)
                 (when t-types
                   (set-box! t-types (pred-env-merge (unbox t-types) (unbox t-types3) '())))])
              (cond
                [(predicate-implies? (unbox r3) 'bottom?) ;check bottom first
                 (when t-types
                   (set-box! t-types (unbox t-types2)))
                 (when f-types
                   (set-box! f-types (unbox f-types2)))
                 (set-box! ret (unbox r2))
                 (set-box! types (unbox t-types1))]
                [(predicate-implies-not? (unbox r3) false-rec)
                 (when f-types
                   (set-box! f-types (pred-env-merge (unbox f-types) (unbox f-types2) '())))]
                [(predicate-implies? (unbox r3) false-rec)
                 (when t-types
                   (set-box! t-types (pred-env-merge (unbox t-types) (unbox t-types2) '())))])
              (cond ; TODO: Use a beter method to unify the ret types.
                [(predicate-implies? (unbox r2) (unbox r3))
                 (set-box! ret (unbox r3))]
                [(predicate-implies? (unbox r3) (unbox r2))
                 (set-box! ret (unbox r2))]
                [(and (eq? ctxt 'test)
                      (predicate-implies-not? (unbox r2) false-rec)
                      (predicate-implies-not? (unbox r3) false-rec))
                 (set-box! ret true-rec)]
                [(find (lambda (t)
                         (and (predicate-implies? (unbox r2) t)
                              (predicate-implies? (unbox r3) t)))
                       '(boolean? char? gensym? symbol? ; lookup is slightly more efficient without boolean?
                         fixnum? integer? number?)) ; ensure they are order from less restrictive to most restrictive
                 => (lambda (t)
                      (set-box! ret t))]
                [else (void)])
              `(if ,e1 ,e2 ,e3))]))]
      [(set! ,maybe-src ,x ,[cptypes : e 'value (box #f) types #f #f -> e])
       (set-box! ret void-rec)
       `(set! ,maybe-src ,x ,e)]
      [(call ,preinfo ,pr ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f))
                       e* r* t*)]
              [ir `(call ,preinfo ,pr ,e* ...)])
         (for-each (lambda (t) (set-box! types (pred-env-merge (unbox types) (unbox t) '()))) t*)
         (set-box! ret (primref->result-predicate pr))
         (for-each (lambda (e n)
                     (let ([pred (primref->argument-predicate pr n)])
                       (set-box! types (pred-env-add/ref (unbox types) e pred))))
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
                [(or (predicate-implies-not? (unbox r1) (unbox r2))
                     (predicate-implies-not? (unbox r2) (unbox r1)))
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect e1 e2) false-rec)]
                [else
                 (when t-types
                   (set-box! t-types (unbox types))
                   (set-box! t-types (pred-env-add/ref (unbox t-types) e1 (unbox r2)))
                   (set-box! t-types (pred-env-add/ref (unbox t-types) e2 (unbox r1))))
                 ir]))]
           [(and (fx= (length e*) 1)
                 (primref->predicate pr #f))
            (let ([pred (primref->predicate pr #f)]
                  [var (unbox (car r*))])
              (cond
                [(predicate-implies? var pred)
                 (set-box! ret true-rec)
                 (make-seq ctxt (car e*) true-rec)]
                [(predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else
                 (when t-types
                   (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                 ir]))]
           [(and (fx= (length e*) 1)
                 (primref->predicate pr #t))
            (let ([pred (primref->predicate pr #t)]
                  [var (unbox (car r*))])
              (cond
                ; no (pred? <ext-pred?>) => #t
                [(predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (car e*) false-rec)]
                [else
                 (when t-types
                   (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                 ir]))]
           [(and (fx>= (length e*) 1)
                 (eq? (primref-name pr) 'record))
            (set-box! ret (rtd->record-predicate (car e*)))
            ir]
           [(and (fx= (length e*) 2)
                 (eq? (primref-name pr) 'record?))
            (let ([pred (rtd->record-predicate (cadr e*))]
                  [var (unbox (car r*))])
              (cond
                [(predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) false-rec)]
                [(and (not (eq? pred '$record?)) ; assume that the only extension is '$record?
                      (predicate-implies? var pred))
                 (set-box! ret true-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) true-rec)]
                [else
                 (when t-types
                   (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                 ir]))]
           [(and (fx= (length e*) 2)
                 (eq? (primref-name pr) '$sealed-record?))
            (let ([pred (rtd->record-predicate (cadr e*))]
                  [var (unbox (car r*))])
              (cond
                [(predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) false-rec)]
                [(and (not (eq? pred '$record?)) ; assume that the only extension is '$record?
                      (pair? pred) (pair? (cdr pred)) (eq? (car pred) '$record?) ;just in case
                      (record-type-descriptor? (cadr pred))
                      (record-type-sealed? (cadr pred))
                      (predicate-implies? var pred))
                 (set-box! ret true-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) true-rec)]
                [else
                 (when t-types
                   (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                 ir]))]
           ; TODO: special case for call-with-values.
           [else
            ir]))]
      [(case-lambda ,preinfo ,cl* ...)
       (let* ([cl* (map (lambda (cl)
                         (nanopass-case (Lsrc CaseLambdaClause) cl
                           [(clause (,x* ...) ,interface ,body)
                            (let ([body (cptypes body 'value (box #f) (box (unbox types)) #f #f)])
                              (with-output-language (Lsrc CaseLambdaClause)
                                `(clause (,x* ...) ,interface ,body)))]))
                        cl*)])
         #;(set-box! ret 'procedure?) ; Disabled until lookup is more efficient
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t (box #f) (box #f))) e* r* t*)]
              [e0 (nanopass-case (Lsrc Expr) e0
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
                     ; We are sure that body will run and that it will be run after the evaluation of the arguments,
                     ; so we can use the types discovered in the arguments and also use the ret and types from the body. 
                     (guard (fx= interface (length x*)))
                     (for-each (lambda (t) (set-box! types (pred-env-merge (unbox types) (unbox t) '()))) t*)
                     (let ([subtypes (box (unbox types))])
                       (for-each (lambda (x r) (set-box! subtypes (pred-env-add (unbox subtypes) x (unbox r)))) x* r*)
                       (let* ([t-subtypes (and t-types (box #f))]
                              [f-subtypes (and f-types (box #f))]
                              [body (cptypes body ctxt ret subtypes t-subtypes f-subtypes)])
                         (set-box! types (pred-env-merge (unbox types) (unbox subtypes) x*))
                         (when t-types
                           (unless (eq? (unbox t-subtypes) (unbox subtypes))
                             (set-box! t-types (pred-env-merge (unbox types) (unbox t-subtypes) x*))))
                         (when f-types
                           (unless (eq? (unbox f-subtypes) (unbox subtypes))
                             (set-box! f-types (pred-env-merge (unbox types) (unbox f-subtypes) x*))))
                         `(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))))]
                    [(case-lambda ,preinfo ,cl* ...)
                     ; We are sure that it will run after the arguments are evaluated,
                     ; so we can effectively delay the evaluation of the lamba and use more types inside it.
                     ; TODO: (difficult) Try to use the ret vales and discovered types. 
                     (for-each (lambda (t) (set-box! types (pred-env-merge (unbox types) (unbox t) '()))) t*)
                     (cptypes e0 'value (box #f) types #f #f)]
                    [else
                     ; It's difficult to be sure the order the code will run,
                     ; so assume that the expresion may be evaluated before the arguments.
                      (let* ([r0 (box #f)]
                             [e0 (cptypes e0 'value r0 types #f #f)])
                        (for-each (lambda (t) (set-box! types (pred-env-merge (unbox types) (unbox t) '()))) t*)
                        #;(set-box! types (pred-env-add/ref (unbox types) e0 'procedure?)) ; Disabled until lookup is more efficient
                        e0)])])
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ((,x* ,e*) ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t (box #f) (box #f))) e* r* t*)]
              [subtypes (box (unbox types))])
         (for-each (lambda (t) (set-box! subtypes (pred-env-merge (unbox subtypes) (unbox t) '()))) t*)
         (for-each (lambda (x r) (set-box! subtypes (pred-env-add (unbox subtypes) x (unbox r)))) x* r*)
         (let* ([t-subtypes (and t-types (box #f))]
                [f-subtypes (and f-types (box #f))]
                [body (cptypes body ctxt ret subtypes t-subtypes f-subtypes)])
           (set-box! types (pred-env-merge (unbox types) (unbox subtypes) x*))
           (when t-types
             (unless (eq? (unbox t-subtypes) (unbox subtypes))
               (set-box! t-types (pred-env-merge (unbox types) (unbox t-subtypes) x*))))
           (when f-types
             (unless (eq? (unbox f-subtypes) (unbox subtypes))
               (set-box! f-types (pred-env-merge (unbox types) (unbox f-subtypes) x*))))
           `(letrec ((,x* ,e*) ...) ,body)))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([subtypes (box (unbox types))]
              [e* (let loop ([x* x*] [e* e*] [rev-e* '()])
                    (if (null? x*)
                        (reverse rev-e*)
                        (let* ([r (box #f)]
                               [e (cptypes (car e*) 'value r subtypes #f #f)])
                           (set-box! subtypes (pred-env-add (unbox subtypes) (car x*) (unbox r)))
                           (loop (cdr x*) (cdr e*) (cons e rev-e*)))))]
              [t-subtypes (and t-types (box #f))]
              [f-subtypes (and f-types (box #f))]
              [body (cptypes body ctxt ret subtypes t-subtypes f-subtypes)])
         (set-box! types (pred-env-merge (unbox types) (unbox subtypes) x*))
         (when t-types
           (unless (eq? (unbox t-subtypes) (unbox subtypes))
             (set-box! t-types (pred-env-merge (unbox types) (unbox t-subtypes) x*))))
         (when f-types
           (unless (eq? (unbox f-subtypes) (unbox subtypes))
             (set-box! f-types (pred-env-merge (unbox types) (unbox f-subtypes) x*))))
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr
       (when (all-set? (prim-mask proc) (primref-flags pr))
         (set-box! ret 'procedure?))
       ir]
      [(foreign ,conv ,name ,[cptypes : e 'value (box #f) types #f #f -> e] (,arg-type* ...) ,result-type)
       `(foreign ,conv ,name ,e (,arg-type* ...) ,result-type)]
      [(fcallable ,conv ,[cptypes : e 'value (box #f) types #f #f -> e] (,arg-type* ...) ,result-type)
       `(fcallable ,conv ,e (,arg-type* ...) ,result-type)]
      [(record ,rtd ,rtd-expr ,e* ...)
       (let* ([types-rtd-expr (box (unbox types))]
              [rtd-expr (cptypes rtd-expr 'value (box #f) types-rtd-expr #f #f)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e t) (cptypes e 'value (box #f) t #f #f)) e* t*)])
         (set-box! types (unbox types-rtd-expr))
         (for-each (lambda (t) (set-box! types (pred-env-merge (unbox types) (unbox t) '()))) t*)
         (set-box! ret (rtd->record-predicate rtd))
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e 'value (box #f) types #f #f -> e])
       (set-box! types (pred-env-add/ref (unbox types) e (rtd->record-predicate rtd)))
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can be reordered?
       (let* ([t1 (box (unbox types))]
              [t2 (box (unbox types))]
              [e1 (cptypes e1 'value (box #f) t1 #f #f)]
              [e2 (cptypes e2 'value (box #f) t2 #f #f)])
         (set-box! types (pred-env-merge (unbox types) (unbox t1) '()))
         (set-box! types (pred-env-merge (unbox types) (unbox t2) '()))
         (set-box! types (pred-env-add/ref (unbox types) e1 (rtd->record-predicate rtd)))
         `(record-set! ,rtd ,type ,index ,e1 ,e2))]
      [(record-type ,rtd ,[cptypes : e 'value (box #f) types #f #f -> e])
       `(record-type ,rtd ,e)]
      [(record-cd ,rcd ,rtd-expr ,[cptypes : e 'value (box #f) types #f #f -> e])
       `(record-cd ,rcd ,rtd-expr ,e)]
      [(immutable-list (,e* ...) ,e)
       (let* ([e* (map (lambda (e) (cptypes e 'value (box #f) (box (unbox types)) #f #f)) e*)]
              [e (cptypes e 'value ret types #f #f)]) #;CHECK
         `(immutable-list (,e*  ...) ,e))]
      [(moi) ir]
      [(pariah) ir]
      [(cte-optimization-loc ,box0 ,[cptypes : e 'value (box #f) types #f #f -> e]) ;don't shadow box
       `(cte-optimization-loc ,box0 ,e)]
      [(cpvalid-defer ,e) (sorry! who "cpvalid leaked a cpvalid-defer form ~s" ir)]
      [(profile ,src) ir]
      #;[else ir]
      [else ($oops who "unrecognized record ~s" ir)]]]

  (define (cptypes ir ctxt ret types t-types f-types)
    (let ([ir (cptypes/raw ir ctxt ret types t-types f-types)])
      (when t-types
        (unless (unbox t-types)
          (set-box! t-types (unbox types))))
      (when f-types
        (unless (unbox f-types)
          (set-box! f-types (unbox types))))
      ir))

  (lambda (x)
    (cptypes x 'value (box #f) (box pred-env-empty) #f #f))
))
