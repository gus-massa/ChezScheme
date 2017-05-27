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
   types [in/out]: a box with a immutable dictionary (currently an intmap).
                   The dictionary connects the counter of a prelex with
                   the discovered types.
                   (fxmap ([prelex-counter x] . 'pair)
                          ([prelex-counter y] . 'vector)
                          ([prelex-counter z] . `(quote 0)))
   t-types [out]: a box to return the types to be used in case the expression
                  is not #f, to be used in the "then" branch of an if.
                  Fill only when you fill ret.
                  If left blank (box #f) it will be automatically filled with a
                  copy of types.
                  It may also be #f (not a box) when the calling function will
                  ignore it.
   f-types [out]: idem for the "else" branch. (if x (something) (here x is #f))


 - predicate: They may be:
              * a symbol to indicate the type, like 'vector 'pair 'number
                (there are a few fake values, in particular 'bottom is used to
                 signal that there is an error)
              * a nanopass-quoted value that is okay-to-copy?, like
                `(quote 0) `(quote 5) `(quote #t) `(quote '())
                (this doesn't includes `(quote <record-type-descriptor>))
              * a [normal] list ($record/rtd <rtd>) to signal that it's a
                record of type <rtd>
              * a [normal] list ($record/ref <ref>) to signal that it's a
                record of a type that is stored in the variable <ref>
                (these may collide with other records)
              * TODO?: add something to indicate that x is a procedure to
                       create/setter/getter/predicate of a record of that type

 - Primitives are marked as procedures, without distinction.
 - Most of the time I'm using eq? and eqv? as if they were equivalent.
   I assume that the differences are hidden by unspecified behavior.

|#


(define $cptypes
(let ()
  (import (nanopass))
  (include "base-lang.ss")
  (include "fxmap.ss")

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
        [(record-type ,rtd ,e) (simple? e)]
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

  (module (pred-env-empty pred-env-add pred-env-intersect pred-env-union
           pred-intersect pred-union pred-env-lookup)
    (import fxmap)

    (define pred-env-empty empty-fxmap)

    (define (pred-env-add types x pred)
      (cond
        [(and x
              pred
              (not (eq? pred 'ptr)) ; filter 'ptr to reduce the size
              (not (prelex-was-assigned x)))
         (let ([old (pred-env-ref/raw types x)])
           (cond
             [(not old)
              (pred-env-add/raw types x pred)]
             [else (let ([new (pred-intersect old pred)])
                     (if (eq? old new)
                         types
                         (pred-env-add/raw types x new)))]))]
        [else types]))

    (define (pred-env-add/raw types x pred)
      (fxmap-set types (prelex-counter x) pred))

    ; This is conceptually the intersection of the types in `types` and `from`
    ; but since 'ptr is not stored to save space and time, the implementation
    ; uses the union of the fxmaps.
    ; [missing 'ptr] _and_ 'vector -> 'vector
    ; 'box _and_ 'vector -> 'bottom
    (define (pred-env-intersect types from)
      (fxmap-union pred-intersect
                   types
                   from))

    (define (pred-intersect x y)
      (cond
        [(predicate-implies? x y) x]
        [(predicate-implies? y x) y]
        [(or (predicate-implies-not? x y)
             (predicate-implies-not? y x))
         'bottom]
        [else (or x y)])) ; if there is no exact option, at least keep the old value

    ; This is conceptually the union of the types in `types` and `from`
    ; but since 'ptr is not stored to save space and time, the implementation
    ; uses the intersection of the fxmaps.
    ; [missing 'ptr] _or_ 'vector -> [missing 'ptr]
    ; 'box _or_ 'vector -> [missing 'ptr]
    ; 'number _or_ 'exact-integer -> number
    (define (pred-env-union types from)
      (fxmap-intersect pred-union
                       types
                       from))

    (define (pred-union x y)
      (cond
        [(predicate-implies? y x) x]
        [(predicate-implies? x y) y]
        [(find (lambda (t)
                 (and (predicate-implies? x t)
                      (predicate-implies? y t)))
               '(boolean char null-or-pair gensym symbol
                 fixnum exact-integer flonum real number))] ; ensure they are order from more restrictive to less restrictive
        [else #f]))

    (define (pred-env-lookup types x)
      (and (not (prelex-was-assigned x))
           (pred-env-ref/raw types x)))

    (define (pred-env-ref/raw types x)
      (fxmap-ref types (prelex-counter x) #f))
  )

  (define (pred-env-add/ref types r pred)
    (nanopass-case (Lsrc Expr) r
      [(ref ,maybe-src ,x)
       (pred-env-add types x pred)]
      [else types]))

  ;copied from cp0.ss
  (define (arity-okay? arity n)
    (or (not arity) ; presumably system routine w/no recorded arity
        (ormap
          (lambda (a)
            (or (fx= n a)
                (and (fx< a 0) (fx>= n (fx- -1 a)))))
          arity)))

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
      [(#3%$record? d) '$record] ;check first to avoid double representation of rtd
      [(okay-to-copy? d) ir]
      [(and (integer? d) (exact? d)) 'exact-integer]
      [(pair? d) 'pair]
      [(box? d) 'box]
      [(vector? d) 'vector]
      [(string? d) 'string]
      [(bytevector? d) 'bytevector]
      [(fxvector? d) 'fxvector]
      [else #f]))

  (define (rtd->record-predicate rtd)
    (cond
      [(Lsrc? rtd)
       (nanopass-case (Lsrc Expr) rtd
         [(quote ,d)
          (guard (record-type-descriptor? d))
          (list '$record/rtd d)]
         [(ref ,maybe-src ,x)
          (guard (not (prelex-was-assigned x)))
          (list '$record/ref x)]
         [(record-type ,rtd ,e)
          (rtd->record-predicate e)]
         [else '$record])]
      [else '$record]))

  ; when extend is #f the result is a predicate that recognizes less values
  ; than the one in name. This is useful for reductions like
  ; (pred? x) ==> #t and (something x) ==> (#3%something x)
  ; when extend is #t the result is a predicate that recognizes more values
  ; than the one in name. This is useful for reductions like
  ; (pred? x) ==> #f and (something x) ==> <error>
  ; in case the non extended version is not #f, the extended version must be not #f
  (define (primref-name->predicate name extend?)
    (case name
      [pair? 'pair]
      [box? 'box]
      [$record? '$record]
      [fixnum? 'fixnum]
      [flonum? 'flonum]
      [real? 'real]
      [number? 'number]
      [vector? 'vector]
      [string? 'string]
      [bytevector? 'bytevector]
      [fxvector? 'fxvector]
      [gensym? 'gensym]
      [symbol? 'symbol]
      [char? 'char]
      [boolean? 'boolean]
      [procedure? 'procedure]
      [not false-rec]
      [null? null-rec]
      [eof-object? eof-rec]
      [bwp-object? bwp-rec]
      [list? (if (not extend?) null-rec 'null-or-pair)]
      [else ((if extend? cdr car);---------------------------------------------------
             (case name
               [(record? record-type-descriptor?) '(bottom . $record)]
               [(integer? rational?) '(exact-integer . real)]
               [(cflonum?) '(flonum . number)]
               [else '(#f . #f)]))])) ; this is used only to detect predicates.

  ; nqm: no question mark
  ; this is almost duplicated code, but with more cases
  ; it's also useful to avoid the allocation
  ; of the temporal strings to transform: vector -> vector?
  (define (primref-name/nqm->predicate name extend?)
    (case name
      [pair 'pair]
      [box 'box]
      [$record '$record]
      [fixnum 'fixnum]
      [flonum 'flonum]
      [real 'real]
      [number 'number]
      [vector 'vector]
      [string 'string]
      [bytevector 'bytevector]
      [fxvector 'fxvector]
      [gensym 'gensym]
      [symbol 'symbol]
      [char 'char]
      [bottom 'bottom] ;pseudo-predicate
      [ptr 'ptr] ;pseudo-predicate
      [boolean 'boolean]
      [procedure 'procedure]
      [exact-integer 'exact-integer] ;fake-predicate
      [void void-rec] ;fake-predicate
      [null null-rec]
      [eof-object eof-rec]
      [bwp-object bwp-rec]
      [list (if (not extend?) null-rec 'null-or-pair)] ;fake-predicate
      [else ((if extend? cdr car);---------------------------------------------------
             (case name
               [(record rtd) '(bottom . $record)]
               [(bit length ufixnum pfixnum) '(bottom . fixnum)]
               [(uint sub-uint) '(bottom . exact-integer)]
               [(sint) '(fixnum . exact-integer)]
               [(uinteger) '(bottom . real)]
               [(integer rational) '(exact-integer . real)]
               [(cflonum) '(flonum . number)]
               [else '(bottom . ptr)]))])) ; this is used only to analyze the signatures.

  (define (primref->predicate pr extend?)
    (primref-name->predicate (primref-name pr) extend?))

  (define (check-constant-is? x pred?)
    (nanopass-case (Lsrc Expr) x
      [(quote ,d) (pred? d)]
      [else #f]))

  ; strange properties of bottom here:
  ; (implies? x bottom): only for x=bottom
  ; (implies? bottom y): always
  ; (implies-not? x bottom): never
  ; (implies-not? bottom y): never
  ; check (implies? x bottom) before (implies? x something)
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
             (and (pair? x) (pair? (cdr x)) (eq? (car x) '$record/rtd)
                  (pair? y) (pair? (cdr y)) (eq? (car y) '$record/rtd)
                  (let loop ([x (cadr x)] [y (cadr y)])
                    (or (eqv? x y)
                        (let ([xp (record-type-parent x)])
                          (and xp (loop xp y))))))
             (and (pair? x) (pair? (cdr x)) (eq? (car x) '$record/ref)
                  (pair? y) (pair? (cdr y)) (eq? (car y) '$record/ref)
                  (eq? (cadr x) (cadr y)))
             (eq? x 'bottom)
             (case y
               [(null-or-pair) (or (check-constant-is? x null?)
                                   (eq? x 'pair))]
               [(fixnum) (check-constant-is? x target-fixnum?)]
               [(exact-integer)
                (or (eq? x 'fixnum)
                    (check-constant-is? x (lambda (x) (and (integer? x)
                                                           (exact? x)))))]
               [(flonum) (check-constant-is? x flonum?)]
               [(real) (or (eq? x 'fixnum)
                           (eq? x 'exact-integer)
                           (eq? x 'flonum)
                           (check-constant-is? x real?))]
               [(number) (or (eq? x 'fixnum)
                             (eq? x 'exact-integer)
                             (eq? x 'flonum)
                             (eq? x 'real)
                             (check-constant-is? x number?))]
               [(gensym) (check-constant-is? x gensym?)]
               [(symbol) (or (eq? x 'gensym)
                             (check-constant-is? x symbol?))]
               [(char) (check-constant-is? x char?)]
               [(boolean) (or (check-constant-is? x not)
                              (check-constant-is? x (lambda (x) (eq? x #t))))]
               [($record) (or (check-constant-is? x #3%$record?)
                              (and (pair? x) (eq? (car x) '$record/rtd))
                              (and (pair? x) (eq? (car x) '$record/ref)))]
               [(vector) (check-constant-is? x vector?)] ; i.e. '#()
               [(string) (check-constant-is? x string?)] ; i.e. ""
               [(bytevector) (check-constant-is? x bytevector?)] ; i.e. '#vu8()
               [(fxvector) (check-constant-is? x fxvector?)] ; i.e. '#vfx()
               [(ptr) #t]
               [else #f]))))

  (define (predicate-implies-not? x y)
    (and x
         y
         ; a $record/ref may be any other kind or record
         (not (and (pair? x)
                   (eq? (car x) '$record/ref)
                   (predicate-implies? y '$record)))
         (not (and (pair? y)
                   (eq? (car y) '$record/ref)
                   (predicate-implies? x '$record)))
         ; the other types are included or disjoint
         (not (predicate-implies? x y))
         (not (predicate-implies? y x))))

  (define (signature->result-predicate signature extend?)
    (let ([results (cdr signature)])
      (and (fx= (length results) 1)
           (let ([result (car results)])
             (cond
               [(symbol? result)
                (primref-name/nqm->predicate result extend?)]
               [(equal? result '(ptr . ptr))
                'pair]
               [(and extend? (pair? result))
                'pair]
               [else
                #f])))))

  (define primref->result-predicate/cache (make-hashtable equal-hash equal?))

  (define (primref->result-predicate pr extend?)
    (let ([key (list (primref-name pr) extend?)])
      (if (hashtable-contains? primref->result-predicate/cache key)
          (hashtable-ref primref->result-predicate/cache key #f)
          (let ([new (primref->result-predicate/no-cache pr extend?)])
            (hashtable-set! primref->result-predicate/cache key new)
            new))))

  (define (primref->result-predicate/no-cache pr extend?)
    (cond
      [(all-set? (prim-mask abort-op)
                 (primref-flags pr))
       'bottom]
      [else
       (let ([signatures (primref-signatures pr)])
         (and (>= (length signatures) 1)
              (let ([results (map (lambda (s) (signature->result-predicate s extend?)) signatures)])
                (fold-left (if extend? pred-union pred-intersect) (car results) (cdr results)))))]))

  (define (signature->argument-predicate signature pos extend?)
    (let* ([arguments (car signature)]
           [dots (memq '... arguments)])
      (cond
        [(and dots (null? (cdr dots)))
         (cond
           [(< pos (- (length arguments) 2))
            (primref-name/nqm->predicate (list-ref arguments pos) extend?)]
           [else
            (primref-name/nqm->predicate (list-ref arguments (- (length arguments) 2)) extend?)])]
         [dots #f] ; TODO: Extend to handle this case, perhaps knowing the argument count.
         [else
          (cond
            [(< pos (length arguments))
             (let ([argument (list-ref arguments pos)])
               (cond
                 [(equal? argument '(ptr . ptr))
                  'pair]
                 [(and extend? (pair? argument))
                  'pair]
                 [else
                  (primref-name/nqm->predicate argument extend?)]))]
            [else
             'bottom])])))

  (define primref->argument-predicate/cache (make-hashtable equal-hash equal?))

  (define (primref->argument-predicate pr pos extend?)
    (let ([key (list (primref-name pr) pos extend?)])
      (if (hashtable-contains? primref->argument-predicate/cache key)
          (hashtable-ref primref->argument-predicate/cache key #f)
          (let ([new (primref->argument-predicate/no-cache pr pos extend?)])
            (when (<= pos 10)
              (hashtable-set! primref->argument-predicate/cache key new))
            new))))

  (define (primref->argument-predicate/no-cache pr pos extend?)
    (let ([signatures (primref-signatures pr)])
      (and (>= (length signatures) 1)
           (let ([vals (map (lambda (signature)
                              (signature->argument-predicate signature pos extend?))
                            signatures)])
             (fold-left (if extend? pred-union pred-intersect) (car vals) (cdr vals))))))

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
           [(predicate-implies? (unbox r1) 'bottom)
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
           [(predicate-implies? (unbox r1) 'bottom) ;check bottom first
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
              (cond
                [(predicate-implies? (unbox r2) 'bottom) ;check bottom first
                 (when t-types
                   (set-box! t-types (unbox t-types3)))
                 (when f-types
                   (set-box! f-types (unbox f-types3)))
                 (set-box! ret (unbox r3))
                 (set-box! types (unbox f-types1))]
                [(predicate-implies-not? (unbox r2) false-rec)
                 (when f-types
                   (set-box! f-types (unbox f-types3)))]
                [(predicate-implies? (unbox r2) false-rec)
                 (when t-types
                   (set-box! t-types (unbox t-types3)))])
              (cond
                [(predicate-implies? (unbox r3) 'bottom) ;check bottom first
                 (when t-types
                   (set-box! t-types (unbox t-types2)))
                 (when f-types
                   (set-box! f-types (unbox f-types2)))
                 (set-box! ret (unbox r2))
                 (set-box! types (unbox t-types1))]
                [(predicate-implies-not? (unbox r3) false-rec)
                 (when f-types
                   (set-box! f-types (unbox f-types2)))]
                [(predicate-implies? (unbox r3) false-rec)
                 (when t-types
                   (set-box! t-types (unbox t-types2)))])
              (unless (or (predicate-implies? (unbox r2) 'bottom)
                          (predicate-implies? (unbox r3) 'bottom))
                (set-box! types (pred-env-union (unbox t-types1) (unbox f-types1)))
                (when (and t-types
                           (not (unbox t-types)) ; t-types doesn't have a value yet
                           (or (not (eq? (unbox t-types1) (unbox t-types2)))
                               (not (eq? (unbox f-types1) (unbox t-types3)))))
                  ; don't calculate t-types when it will be equal to types
                  (set-box! t-types (pred-env-union (unbox t-types2) (unbox t-types3))))
                (when (and f-types
                           (not (unbox f-types)) ; f-types doesn't have a value yet
                           (or (not (eq? (unbox t-types1) (unbox f-types2)))
                               (not (eq? (unbox f-types1) (unbox f-types3)))))
                  ; don't calculate f-types when it will be equal to types
                  (set-box! f-types (pred-env-union (unbox f-types2) (unbox f-types3))))
                  (set-box! ret (pred-union (unbox r2) (unbox r3)))
                  (when (and (eq? ctxt 'test)
                             (predicate-implies-not? (unbox r2) false-rec)
                             (predicate-implies-not? (unbox r3) false-rec))
                    ; special case in test context
                   (set-box! ret true-rec)))
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
         (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
         (set-box! ret (primref->result-predicate pr #t))
         (for-each (lambda (e r n)
                     (let ([pred (primref->argument-predicate pr n #t)])
                       (set-box! types (pred-env-add/ref (unbox types) e pred))
                       (when (predicate-implies-not? (unbox r) pred)
                         (set-box! ret 'bottom))))
                   e* r* (enumerate e*))
         (cond
           [(predicate-implies? (unbox ret) 'bottom)
            ir]
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
                 (primref->predicate pr #t))
            (let ([var (unbox (car r*))])
              (let ([pred (primref->predicate pr #f)])
                (cond
                  [(predicate-implies? var pred)
                   (set-box! ret true-rec)
                   (make-seq ctxt (car e*) true-rec)]
                  [else
                   (let ([pred (primref->predicate pr #t)])
                     (cond
                       [(predicate-implies-not? var pred)
                        (set-box! ret false-rec)
                        (make-seq ctxt (car e*) false-rec)]
                       [else
                        (when t-types
                          (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                        ir]))])))]
           [(and (fx>= (length e*) 1)
                 (eq? (primref-name pr) '$record))
            (set-box! ret (rtd->record-predicate (car e*)))
            ir]
           [(and (fx= (length e*) 2)
                 (eq? (primref-name pr) 'record?))
            (let ([pred (rtd->record-predicate (cadr e*))]
                  [var (unbox (car r*))])
              (cond
                [(predicate-implies-not? var pred)
                 (set-box! ret false-rec)
                 (cond
                   [(or (not (all-set? (prim-mask unsafe) (primref-flags pr)))
                        (nanopass-case (Lsrc Expr) (cadr e*) ; ensure that it is actually a rtd
                          [(quote ,d)
                           (record-type-descriptor? d)]
                          [(record-type ,rtd ,e) #t]
                          [else #f]))
                    (make-seq ctxt ir false-rec)]
                   [else
                    (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) false-rec)])]
                [(and (not (eq? pred '$record)) ; assume that the only extension is '$record
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
                [(and (not (eq? pred '$record)) ; assume that the only extension is '$record
                      (predicate-implies? var pred))
                 (set-box! ret true-rec)
                 (make-seq ctxt (make-seq 'effect (car e*) (cadr e*)) true-rec)]
                [else
                 (when t-types
                   (set-box! t-types (pred-env-add/ref (unbox types) (car e*) pred)))
                 ir]))]
           ; TODO: special case for call-with-values.
           [(not (arity-okay? (primref-arity pr) (length e*)))
            (set-box! ret 'bottom)
            ir]
           [(and (fx= (length e*) 1)
                 (eq? (primref-name pr) 'exact?))
            (cond
              [(predicate-implies? (unbox (car r*)) 'fixnum)
               (set-box! ret true-rec)
               true-rec]
              [(predicate-implies? (unbox (car r*)) 'flonum)
               (set-box! ret false-rec)
               false-rec]
              [else
               ir])]
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
         (set-box! ret 'procedure)
         `(case-lambda ,preinfo ,cl* ...))]
      [(call ,preinfo ,e0 ,e* ...)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f)) e* r* t*)]
              [e0 (nanopass-case (Lsrc Expr) e0
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
                     ; We are sure that body will run and that it will be run after the evaluation of the arguments,
                     ; so we can use the types discovered in the arguments and also use the ret and types from the body.
                     (guard (fx= interface (length e*)))
                     (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
                     (for-each (lambda (x r) (set-box! types (pred-env-add (unbox types) x (unbox r)))) x* r*)
                     (let ([body (cptypes body ctxt ret types t-types f-types)])
                       `(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)))]
                    [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
                     ; We are sure that body will run and that it will be run after the evaluation of the arguments,
                     ; but this will raise an error. TODO: change body to (void) because it will never run.
                     (guard (not (fx= interface (length e*))))
                     (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
                     (set-box! ret 'bottom)
                     (let ([body (cptypes body ctxt (box #f) types #f #f)])
                       `(case-lambda ,preinfo (clause (,x* ...) ,interface ,body)))]
                    [(case-lambda ,preinfo ,cl* ...)
                     ; We are sure that it will run after the arguments are evaluated,
                     ; so we can effectively delay the evaluation of the lambda and use more types inside it.
                     ; TODO: (difficult) Try to use the ret vales and discovered types.
                     (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
                     (cptypes e0 'value (box #f) types #f #f)]
                    [else
                     ; It's difficult to be sure the order the code will run,
                     ; so assume that the expression may be evaluated before the arguments.
                      (let* ([r0 (box #f)]
                             [e0 (cptypes e0 'value r0 types #f #f)])
                        (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
                        (set-box! types (pred-env-add/ref (unbox types) e0 'procedure))
                        e0)])])
         `(call ,preinfo ,e0 ,e* ...))]
      [(letrec ((,x* ,e*) ...) ,body)
       (let* ([r* (map (lambda (e) (box #f)) e*)]
              [t* (map (lambda (e) (box (unbox types))) e*)]
              [e* (map (lambda (e r t) (cptypes e 'value r t #f #f)) e* r* t*)])
         (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
         (for-each (lambda (x r) (set-box! types (pred-env-add (unbox types) x (unbox r)))) x* r*)
         (let ([body (cptypes body ctxt ret types t-types f-types)])
           `(letrec ((,x* ,e*) ...) ,body)))]
      [(letrec* ([,x* ,e*] ...) ,body)
       (let* ([e* (let loop ([x* x*] [e* e*] [rev-e* '()])  ; this is like an ordered-map
                    (if (null? x*)
                        (reverse rev-e*)
                        (let* ([r (box #f)]
                               [e (cptypes (car e*) 'value r types #f #f)])
                           (loop (cdr x*) (cdr e*) (cons e rev-e*)))))]
              [body (cptypes body ctxt ret types t-types f-types)])
         `(letrec* ([,x* ,e*] ...) ,body))]
      [,pr
       (when (all-set? (prim-mask proc) (primref-flags pr))
         (set-box! ret 'procedure))
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
         (for-each (lambda (t) (set-box! types (pred-env-intersect (unbox types) (unbox t)))) t*)
         (set-box! ret (rtd->record-predicate rtd-expr))
         `(record ,rtd ,rtd-expr ,e* ...))]
      [(record-ref ,rtd ,type ,index ,[cptypes : e 'value (box #f) types #f #f -> e])
       (set-box! types (pred-env-add/ref (unbox types) e '$record))
       `(record-ref ,rtd ,type ,index ,e)]
      [(record-set! ,rtd ,type ,index ,e1 , e2) ;can they be reordered?
       (let* ([t1 (box (unbox types))]
              [t2 (box (unbox types))]
              [e1 (cptypes e1 'value (box #f) t1 #f #f)]
              [e2 (cptypes e2 'value (box #f) t2 #f #f)])
         (set-box! types (unbox t1))
         (set-box! types (pred-env-intersect (unbox types) (unbox t2)))
         (set-box! types (pred-env-add/ref (unbox types) e1 '$record))
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
