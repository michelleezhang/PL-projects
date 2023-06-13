#lang plai/gc2/collector

; initialize the state variables in the heap
(define (init-allocator)
  ; heap address 0 holds the allocation pointer
  (heap-set! 0 4)
  
  ; heap address 1 holds the start of the active space
  (heap-set! 1 4)

  ; heap address 2 holds the start of the queue
  ; heap address 3 holds the end of the queue
  (define midpoint (+ (/ (- (heap-size) 4) 2) 4)) ; calculate the middle of the heap
  (heap-set! 2 midpoint)
  (heap-set! 3 midpoint))

(define (find-free-size)
  (/ (- (heap-size) 4) 2))

(define (find-free-upper-bound)
  (+ (heap-ref 1) (find-free-size)))

; allocator -- set aside _n_ amount of space (update allocation pointer)
(define (malloc n root1 root2)
  (define address (heap-ref 0)) ; find next free spot to allocate in

  (define new-allocation-address (+ address n))

  ; calculate the end of the free space
  (define free-upper-bound (find-free-upper-bound))

  (cond
    [(<= new-allocation-address free-upper-bound) ; check that new address is within the free space
      (heap-set! 0 new-allocation-address) ; update allocation pointer
     address]
    [else
     ; if we're out of memory, garbage collect...
     (collect-garbage root1 root2)

     ; ...and try allocating again
     (define address (heap-ref 0))
     (define new-allocation-address (+ address n))
     (define free-upper-bound (find-free-upper-bound))
     
     ; if we're still out of memory, then we are out of memory fr fr, so error
     (unless (<= new-allocation-address free-upper-bound) 
       (error 'malloc "out of memory"))
    
     (heap-set! 0 new-allocation-address)
     address
     ]))

;; A bunch of allocation stuff for each type of data (just stuff from lecture)
#|
flat:    ... | 'flat | <payload> | ...
|#
;; gc:alloc-flat : flat-value -> address
(define (gc:alloc-flat value)
  (define address (malloc 2 #f #f))
  (heap-set! address 'flat)
  (heap-set! (+ address 1) value)
  address)
;; gc:flat? : address -> boolean
(define (gc:flat? address)
  (equal? (heap-ref address) 'flat))
;; gc:deref : address -> flat-value
(define (gc:deref address)
  (unless (gc:flat? address)
    (error 'gc:deref "expected flat @ ~a" address))
  (heap-ref (+ address 1)))

#|
pair:    ... | 'cons | <first-ptr> | <rest-ptr> | ...
|#
;; gc:cons : root root -> address
(define (gc:cons root1 root2)
  (define address (malloc 3 root1 root2))
  (heap-set! address 'cons)
  (heap-set! (+ address 1) (read-root root1))
  (heap-set! (+ address 2) (read-root root2))
  address)
;; gc:cons? : address -> boolean
(define (gc:cons? address)
  (equal? (heap-ref address) 'cons))
;; gc:first : address -> address
(define (gc:first address)
  (unless (gc:cons? address)
    (error 'gc:first "expected cons @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:rest : address -> address
(define (gc:rest address)
  (unless (gc:cons? address)
    (error 'gc:rest "expected cons @ ~a" address))
  (heap-ref (+ address 2)))
;; gc:set-first! : address address -> void
(define (gc:set-first! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-first! "expected cons @ ~a" address))
  (heap-set! (+ address 1) new-value-address))
;; gc:set-rest! : address address -> void
(define (gc:set-rest! address new-value-address)
  (unless (gc:cons? address)
    (error 'gc:set-rest! "expected cons @ ~a" address))
  (heap-set! (+ address 2) new-value-address))


#|
closure: ... | 'clos | <code-ptr> | <n-free-vars> | <fv0> | <fv1> | ... | ...
|#
;; gc:closure : opaque-value (listof root) -> address
(define (gc:closure code-ptr free-vars)
  (define address (malloc (+ 3 (length free-vars))
                          free-vars
                          #f))
  (heap-set! address 'clos)
  (heap-set! (+ address 1) code-ptr)
  (heap-set! (+ address 2) (length free-vars))
  (for ([fv (in-list free-vars)]
        [i  (in-naturals)])
    (heap-set! (+ address 3 i) (read-root fv)))
  address)
;; gc:closure? : address -> boolean
(define (gc:closure? address)
  (equal? (heap-ref address) 'clos))
;; gc:closure-code-ptr : address -> opaque-value
(define (gc:closure-code-ptr address)
  (unless (gc:closure? address)
    (error 'gc:closure-code-ptr "expected closure @ ~a" address))
  (heap-ref (+ address 1)))
;; gc:closure-env-ref : address integer -> address
(define (gc:closure-env-ref address i)
  (unless (gc:closure? address)
    (error 'gc:closure-env-ref "expected closure @ ~a" address))
  (heap-ref (+ address 3 i)))


; garbage collection
(define (collect-garbage root1 root2)
  ; enqueue all roots -- the enqueue function sets the forwarding pointers as well
  (enqueue/roots (get-root-set))
  (enqueue/roots root1)
  (enqueue/roots root2)
  
  (dequeue-loop))

(define (dequeue-loop)
  (cond
    [(equal? (heap-ref 2) (heap-ref 3))
     ; if the queue is empty, swap spaces!
     (swap-space)]
    [else
     ; while queue is not empty, dequeue -- the dequeue also enqueues any children
    (dequeue)
    (dequeue-loop)]))

(define (enqueue/roots roots)
  (cond [(list? roots) (for-each enqueue/roots roots)]
        [(root? roots)
         ; enqueue each root
         ; need to update the roots after you've enqueued them, hence set-root
         (set-root! roots (enqueue/loc (read-root roots)))]
        [(false? roots) (void)]
        [else (error 'enqueue/roots "unexpected roots: ~a" roots)]))

(define (enqueue/loc node)
  ; enq-ptr is the end of the queue 
  (define enq-ptr (heap-ref 2))

  ; when we enqueue, we do four things:
  ; copy the item into the queue (from-space => to-space)
  ; set forward pointer in the from space
  ; update the enq-ptr
  ; at the very end, return the enq-ptr so we can update roots/parents
  
  [case (heap-ref node)
    [(flat)
     ; copy over 'flat and its value
     (heap-set! enq-ptr 'flat)
     (heap-set! (+ enq-ptr 1) (heap-ref (+ node 1)))
     
     ; set the forward pointer
     (heap-set! node 'f)
     (heap-set! (+ node 1) enq-ptr)

     ; update the enq-ptr
     (heap-set! 2 (+ enq-ptr 2))

     ; return old queue end
     enq-ptr]
    
    [(cons)
     ; copy
     (heap-set! enq-ptr 'cons)
     (heap-set! (+ enq-ptr 1) (heap-ref (+ node 1)))
     (heap-set! (+ enq-ptr 2) (heap-ref (+ node 2)))

     ; forward
     (heap-set! node 'f)
     (heap-set! (+ node 1) enq-ptr)

     ; enq-ptr update
     (heap-set! 2 (+ enq-ptr 3))

     ; return
     enq-ptr]
    
    [(clos)
     ; copy
     (heap-set! enq-ptr 'clos)
     (heap-set! (+ enq-ptr 1) (heap-ref (+ node 1)))
     (define num-fvs (heap-ref (+ node 2)))
     (heap-set! (+ enq-ptr 2) num-fvs)
     (for ([i (in-range num-fvs)])
       (heap-set! (+ enq-ptr (+ 3 i)) (heap-ref (+ node (+ 3 i)))))

     ; forward
     (heap-set! node 'f)
     (heap-set! (+ node 1) enq-ptr)

     ; enq-ptr update
     (heap-set! 2 (+ enq-ptr (+ 3 num-fvs)))

     ; return
     enq-ptr]

    [(f)
     ; if we have repeat roots, move forward by 1
     (heap-ref (+ 1 node))]
    [else
     (error 'enqueue "unexpected tag @ ~a" node)]])

(define (dequeue)
  ; deq-ptr is the start of the queue 
  (define deq-ptr (heap-ref 3))
  
  ; when we dequeue, we do two things:
  ; enqueue any children
  ; update the deq-ptr

  [case (heap-ref deq-ptr)
    [(flat)
     ; update the deq-ptr
     (heap-set! 3 (+ deq-ptr 2))]

    [(cons)
     ; deq-ptr update
     (heap-set! 3 (+ deq-ptr 3))
     
     ; enqueue children
     ; update "roots" (parents) when we enqueue, as always
     (heap-set! (+ deq-ptr 1) (enqueue/loc (heap-ref (+ deq-ptr 1))))
     (heap-set! (+ deq-ptr 2) (enqueue/loc (heap-ref (+ deq-ptr 2))))]
    
    [(clos)
     (define num-fvs (heap-ref (+ deq-ptr 2)))
     ; deq-ptr update
     (heap-set! 3 (+ deq-ptr (+ 3 num-fvs))) ; tag, name, num_fvs, fvs

     ; enqueue children and update parents 
     (for ([i (in-range num-fvs)])
       (heap-set! (+ deq-ptr (+ 3 i)) (enqueue/loc (heap-ref (+ deq-ptr (+ 3 i))))))]
    
    [else
     (error 'dequeue "unexpected tag @ ~a" deq-ptr)]])

(define (swap-space)
  (define old-start (heap-ref 1))
  (define midpoint (+ (/ (- (heap-size) 4) 2) 4))

  ; the next available spot in the new space is always the end of the old queue
  (heap-set! 0 (heap-ref 3))

  (cond
    [(equal? old-start 4)
     ; the free space starts at the midpoint
     (heap-set! 1 midpoint)
     ; the queue pointers begin at 4
     (heap-set! 2 4)
     (heap-set! 3 4)]
    [else
     ; the free space starts at 4
     (heap-set! 1 4)
     ; the queue pointers begin at the midpoint
     (heap-set! 2 midpoint)
     (heap-set! 3 midpoint)]))

;(define (validate-heap start)
;  (define free-upper-bound (find-free-upper-bound))
;  (when (< start free-upper-bound)  ; make sure everything is in the "from" space
;    (case (heap-ref start)
;      [(flat)
;       (validate-heap (+ start 2))] ; make sure each type of data takes up the right amount of space
;      [(cons)
;       (valid-pointer-at? (+ start 1))
;       (valid-pointer-at? (+ start 2))
;       (validate-heap (+ start 3))]
;      [(clos)
;       (unless (heap-value? (heap-ref (+ start 1)))
;         (error 'validate-heap "invalid code pointer @ ~a" start))
;       (unless (natural? (heap-ref (+ start 2)))
;         (error 'validate-heap "invalid number of free variables @ ~a" start))
;       (for ([i (in-range (heap-ref (+ start 2)))])
;         (valid-pointer-at? (+ start 3 i)))
;       (validate-heap (+ start 3 (heap-ref (+ start 2))))]
;      [(#f) (void)]
;      [(f) (void)]
;      [else
;       (error 'validate-heap "unexpected tag @ ~a" start)])))
;
;(define (valid-pointer-at? a)
;  (define free-upper-bound (find-free-upper-bound))
;  (define ptr (heap-ref a))
;  (unless (and (integer? ptr)
;               (< ptr free-upper-bound) ; everything points to the "from" space
;               (>= ptr 0)
;               (member (heap-ref ptr) (list 'flat 'cons 'clos)))
;    (error 'valid-pointer-at? "invalid pointer @ ~a" a)))