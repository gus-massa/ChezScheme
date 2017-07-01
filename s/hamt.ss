;; "hamt.ss"
;; Based on an implementation by Jon Zeppieri

;; Exports:
;;  ($hamt-empty) => hamt
;;  ($hamt-empty? hamt) => boolean?
;;  ($hamt-ref hamt key key-hash-proc key=? default-val) => val or default-val
;;  ($hamt-set hamt key key-hash-proc key=? val) => hamt
;;  ($hamt-remove hamt key key-hash-proc key=?) => hamt
;;  ($hamt-count hamt) => number?
;;  ($hamt-fold hamt acc proc) => any

(module ($hamt-empty $hamt-empty? $hamt-ref $hamt-set $hamt-remove $hamt-count $hamt-fold)
  ;; A bnode and cnode have the same shape:
  ;;  (vector <tag> <bitmap-or-hashcode> <key1> <val1> <key2> <val2> ...)
  ;; A bnode tag is a total count of mapped keys; a cnode tag is 'cnode
  ;; A bnode has a bitmap based on hashes at the node's level.
  ;; A cnode (for collisions) keeps the colliding hashcode.
  ;; A <val> is `*key-is-node*` if the corresponding <key> is a node.
  (define NODE-CONTENT-OFFSET 2)
  
  (define (alloc-node count tag val)
    (let ([vec (make-vector (fx+ NODE-CONTENT-OFFSET (fxsll count 1)))])
      (vector-set! vec 0 tag)
      (vector-set! vec 1 val)
      vec))
  
  (define (node-tag n)
    (vector-ref n 0))
  
  (define (node-extra n) ; bitmap for bnode, hashcode for cnode
    (vector-ref n 1))
  
  (define (node-empty? bnode)
    (fx= NODE-CONTENT-OFFSET (vector-length bnode)))
  
  (define (node-singleton? bnode)
    (fx= (fx+ 2 NODE-CONTENT-OFFSET) (vector-length bnode)))
  
  (define (node-length n)
    (fxsra (fx- (vector-length n) NODE-CONTENT-OFFSET) 1))

  (define (node-count n)
    (let ([t (node-tag n)])
      (if (eq? t 'cnode)
          (node-length n)
          t)))

  (define (node-key-ref node idx)
    (vector-ref node (fx+ NODE-CONTENT-OFFSET (fx+ idx idx))))
  
  (define (node-val-ref node idx)
    (vector-ref node (fx+ (fx+ NODE-CONTENT-OFFSET 1) (fx+ idx idx))))

  (define (node-set! n idx key val)
    (let ([i (fx+ NODE-CONTENT-OFFSET (fx+ idx idx))])
      (vector-set! n i key)
      (vector-set! n (fx1+ i) val)))

  (define (node-copy! dest-n dest-start src-n src-start src-end)
    (unless (= src-start src-end)
      (let ([dest-start (fx+ NODE-CONTENT-OFFSET (fx+ dest-start dest-start))]
            [src-start (fx+ NODE-CONTENT-OFFSET (fx+ src-start src-start))]
            [len (fxsll (fx- src-end src-start) 1)])
        (let loop ([i len])
          (unless (fx= 0 i)
            (let ([i (sub1 i)])
              (vector-set! dest-n (+ dest-start i) (vector-ref src-n (+ src-start i)))
              (loop i)))))))

  (define (tag+ tag delta)
    (if (eq? tag 'cnode)
        'cnode
        (+ tag delta)))

  (define (node-replace-at-index n count-delta idx key val)
    (let* ([len (node-length n)]
           [new (alloc-node len (tag+ (node-tag n) count-delta) (node-extra n))])
      (node-copy! new 0 n 0 idx)
      (node-set! new idx key val)
      (node-copy! new (fx1+ idx) n (fx1+ idx) len)
      new))

  (define (node-insert-at-index n extra idx key val)
    (let* ([len (node-length n)]
           [new (alloc-node (fx1+ len) (tag+ (node-tag n) 1) extra)])
      (node-copy! new 0 n 0 idx)
      (node-set! new idx key val)
      (node-copy! new (fx1+ idx) n idx len)
      new))

  (define (node-remove-at-index n extra idx)
    (let* ([len (node-length n)]
           [new (alloc-node (fx1- len) (tag+ (node-tag n)-1) extra)])
      (node-copy! new 0 n 0 idx)
      (node-copy! new idx n (fx1+ idx) len)
      new))

  ;; ----------------------------------------

  (define empty-bnode (alloc-node 0 0 0))

  (define (bnode? n)
    (not (eq? 'cnode (node-tag n))))
  
  (define (bnode-bitmap bnode)
    (node-extra bnode))

  (define (bnode-index node keyhash shift)
    (let* ([bitmap (bnode-bitmap node)]
           [bit (bnode-bit keyhash shift)])
      (and (bit-set? bitmap bit)
           (bnode-idx bitmap bit))))

  (define (bnode-bit keyhash shift)
    (fxand (fxsra keyhash shift) #x0f))

  (define (bnode-idx bitmap bit)
    (fxbit-count (fxand bitmap (fx- (fxsll 1 bit) 1))))

  (define (bit-set? bitmap bit)
    (fxlogbit? bit bitmap))

  (define (down shift)
    (fx+ shift 4))

  (define (make-cnode2 hashcode k1 v1 k2 v2)
    (let ([cnode (alloc-node 2 'cnode hashcode)])
      (node-set! cnode 0 k1 v1)
      (node-set! cnode 1 k2 v2)
      cnode))

  (define (cnode? n)
    (eq? 'cnode (node-tag n)))

  (define (cnode-hashcode cnode)
    (node-extra cnode))

  (define *key-is-node* (list '*key-is-node*))

  ;; ----------------------------------------
  
  (define (hamt-empty? h)
    (node-empty? h))

  (define (hamt-count h)
    (node-count h))
  
  ;; ----------------------------------------

  (define (hamt-ref h key key->hash key= default)
    (node-ref h key (key->hash key) key= 0 default))

  (define (node-ref node key keyhash key= shift default)
    (if (bnode? node)
        (bnode-ref node key keyhash key= shift default)
        (cnode-ref node key keyhash key= default)))

  (define (bnode-ref bnode key keyhash key= shift default)
    (let ([idx (bnode-index bnode keyhash shift)])
      (cond
       [(not idx) default]
       [else
        (let ([k (node-key-ref bnode idx)]
              [v (node-val-ref bnode idx)])
          (cond
           [(not (eq? v *key-is-node*))
            (cond
             [(key= key k) v]
             [else default])]
           [else (node-ref k key keyhash key= (down shift) default)]))])))

  (define (cnode-ref cnode key keyhash key= default)
    (let ([hashcode (cnode-hashcode cnode)])
      (if (= hashcode keyhash)
          (let ([i (cnode-index cnode key key=)])
            (if i
                (node-val-ref cnode i)
                default))
          default)))

  (define (cnode-index cnode key key=)
    (let ([len (node-length cnode)])
      (let loop ([idx 0])
        (cond
         [(fx= idx len) #f]
         [else
          (let ([k (node-key-ref cnode idx)])
            (if (key= key k)
                idx
                (loop (fx1+ idx))))]))))

  ;; ----------------------------------------
  
  (define (hamt-set h key key->hash key= val)
    (node-set h key val (key->hash key) key= key->hash 0))

  (define (node-set node key val keyhash key= key->hash shift)
    (if (bnode? node)
        (bnode-set node key val keyhash key= key->hash shift)
        (cnode-set node key val keyhash key= key->hash shift)))

  (define (bnode-set bnode key val keyhash key= key->hash shift)
    (let* ([bitmap (bnode-bitmap bnode)]
           [bit (bnode-bit keyhash shift)]
           [idx (bnode-idx bitmap bit)])
      (cond
       [(bit-set? bitmap bit)
        (let ([k (node-key-ref bnode idx)]
              [v (node-val-ref bnode idx)])
          (cond
           [(not (eq? v *key-is-node*))
            (cond
             [(key= key k)
              (node-replace-at-index bnode 0 idx key val)]
             [else
              (let ([child (make-node k v key val keyhash key= key->hash (down shift))])
                (node-replace-at-index bnode +1 idx child *key-is-node*))])]
           [else
            (let ([new-child (node-set k key val keyhash key= key->hash (down shift))])
              (node-replace-at-index bnode (- (node-count new-child) (node-count k)) idx new-child *key-is-node*))]))]
       [else
        (node-insert-at-index bnode (fxior bitmap (fxsll 1 bit)) idx key val)])))

  (define (cnode-set cnode key val keyhash key= key->hash shift)
    (let* ([hashcode (cnode-hashcode cnode)])
      (cond
       [(= hashcode keyhash)
        (let ([idx (cnode-index cnode key key=)])
          (cond
           [idx (node-replace-at-index cnode 0 idx key val)]
           [else (node-insert-at-index cnode hashcode 0 key val)]))]
       [else
        (let ([new (node-insert-at-index empty-bnode (fxsll 1 (bnode-bit hashcode shift)) 0 cnode *key-is-node*)])
          (node-set new key val keyhash key= key->hash shift))])))

  (define (make-node k1 v1 k2 v2 k2hash key= key->hash shift)
    (let ([k1hash (key->hash k1)])
      (cond
       [(= k1hash k2hash)
        (make-cnode2 k1hash k1 v1 k2 v2)]
       [else
        (let ([n (node-set empty-bnode k1 v1 k1hash key= key->hash shift)])
          (node-set n k2 v2 k2hash key= key->hash shift))])))

  ;; ----------------------------------------

  (define (hamt-remove h key key->hash key=)
    (node-remove h key (key->hash key) key= 0))

  (define (node-remove node key keyhash key= shift)
    (if (bnode? node)
        (bnode-remove node key keyhash key= shift)
        (cnode-remove node key keyhash key= shift)))

  (define (bnode-remove bnode key keyhash key= shift)
    (let* ([bitmap (bnode-bitmap bnode)]
           [bit (bnode-bit keyhash shift)]
           [idx (bnode-idx bitmap bit)])
      (cond
       [(bit-set? bitmap bit)
        (let ([k (node-key-ref bnode idx)]
              [v (node-val-ref bnode idx)])
          (cond
           [(not (eq? v *key-is-node*))
            (cond
             [(key= key k)
              (node-remove-at-index bnode (fxxor bitmap (fxsll 1 bit)) idx)]
             [else
              bnode])]
           [else
            (let* ([child k]
                   [child-shift (down shift)]
                   [new-child (node-remove child key keyhash key= child-shift)])
              (cond
               [(eq? child new-child)
                bnode]
               [(contract-node? new-child child-shift)
                (node-replace-at-index bnode -1 idx (node-key-ref new-child 0) (node-val-ref new-child 0))]
               [else
                (node-replace-at-index bnode -1 idx new-child *key-is-node*)]))]))]
       [else bnode])))

  (define (cnode-remove cnode key keyhash key= shift)
    (let ([hashcode (cnode-hashcode cnode)])
      (cond
       [(= hashcode keyhash)
        (let ([idx (cnode-index cnode key key=)])
          (cond
           [idx (node-remove-at-index cnode hashcode idx)]
           [else cnode]))]
       [else cnode])))

  (define (contract-node? n shift)
    (and (node-singleton? n)
         (fx> shift 0)
         (or (not (eq? *key-is-node* (node-val-ref n 0)))
             (not (bnode? (node-key-ref n 0))))))

  ;; ----------------------------------------

  (define (hamt-fold h id proc)
    (node-fold h id proc))
  
  (define (node-fold n acc proc)
    (let ([len (node-length n)])
      (let loop ([acc acc] [idx 0])
        (cond
         [(fx= idx len) acc]
         [else
          (let ([key (node-key-ref n idx)]
                [val (node-val-ref n idx)])
            (if (eq? *key-is-node* val)
                (loop (node-fold key acc proc) (fx1+ idx))
                (loop (proc key val acc) (fx1+ idx))))]))))

  ;; ----------------------------------------

  (define $hamt-empty (lambda () empty-bnode))
  (define $hamt-empty? node-empty?)
  (define $hamt-set hamt-set)
  (define $hamt-ref hamt-ref)
  (define $hamt-remove hamt-remove)
  (define $hamt-count hamt-count)
  (define $hamt-fold hamt-fold)
)
