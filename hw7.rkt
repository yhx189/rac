#lang plai/gc2/collector

(define eight-principles
  (list
   "Know your rights."
   "Acknowledge your sources."
   "Protect your work."
   "Avoid suspicion."
   "Do your own work."
   "Never falsify a record or permit another person to do so."
   "Never fabricate data, citations, or experimental results."
   "Always tell the truth when discussing your work with your instructor."))


;; gc:flat? : location? -> flat-value?
(define (gc:flat? loc)
  (equal? (heap-ref loc) 'flat))

;; gc:deref : location? -> void?
(define (gc:deref loc)
  (cond
    [(equal? (heap-ref loc) 'flat)
     (heap-ref (+ loc 1))]
    [else
     (error 'gc:deref
            "attempted to deref a non flat value, loc ~s"
             loc)]))

;; gc:cons? : location? -> boolean?
(define (gc:cons? loc)
  (equal? (heap-ref loc) 'pair))

;; gc:first : location? -> location?
(define (gc:first pr-ptr)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-ref (+ pr-ptr 1))
      (error 'first "non pair")))

;; gc:rest : location? -> heap-value?
(define (gc:rest pr-ptr)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-ref (+ pr-ptr 2))
      (error 'rest "non pair")))


;; gc:set-first! : location? location? -> void?
(define (gc:set-first! pr-ptr new)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-set! (+ pr-ptr 1) new)
      (error 'set-first! "non pair")))

;; gc:set-rest! : location? location? -> void?
(define (gc:set-rest! pr-ptr new)
  (if (equal? (heap-ref pr-ptr) 'pair)
      (heap-set! (+ pr-ptr 2) new)
      (error 'set-first! "non pair")))

;; gc:closure-code-ptr : loc -> heap-value
(define (gc:closure-code-ptr loc)
  (if (gc:closure? loc)
      (heap-ref (+ loc 1))
      (error 'gc:closure-code "non closure @ ~a, got ~s"
             loc (heap-ref loc))) )

;; gc:closure-env-ref : loc number -> loc
(define (gc:closure-env-ref loc i)
  (if (gc:closure? loc)
      (if (< i (heap-ref (+ loc 2)))
          (heap-ref (+ loc 3 i))
          (error 'closure-env-ref
                 "closure-env-ref out of bounds"))
      (error 'closure-env-ref "non closure")))

;; gc:closure? : loc -> boolean
(define (gc:closure? loc)
  (equal? (heap-ref loc) 'proc))

;; gc:alloc-flat : flat-values? -> location?
(define (gc:alloc-flat fv)
  (let ([ptr (alloc 2 '() '())])
    (heap-set! ptr 'flat)
    (heap-set! (+ ptr 1) fv)
    (heap-set! 1 (+ 2 (heap-ref 1)))
    ptr))

;; gc:cons : root? root? -> location?
(define (gc:cons hd tl)
  (define ptr (alloc 3 hd tl))
  (heap-set! ptr 'pair)
  (heap-set! (+ ptr 1) hd)
  (heap-set! (+ ptr 2) tl)
  (heap-set! 1 (+ 3 (heap-ref 1)))
  ptr)

;; gc:closure : heap-value (vectorof loc) -> loc
(define (gc:closure code-ptr free-vars)
  (define free-vars-count (length free-vars))
  (define next (alloc (+ free-vars-count 3) free-vars '()))
  (heap-set! next 'proc)
  (heap-set! (+ next 1) code-ptr)
  (heap-set! (+ next 2) free-vars-count)
  (for ([x (in-range 0 free-vars-count)]
        [r (in-list free-vars)])
    (heap-set! (+ next 3 x) (read-root r)))
  (heap-set! 1 (+ 3 free-vars-count (heap-ref 1)))
  next)


;; init-allocator : -> void
; put four state variables in the head of heap, ie. allocation pointer, active semispace,
; queue header, queue tail
(define (init-allocator) 
  (heap-set! 0 'flat)
  (heap-set! 1 8)
  (heap-set! 2 'flat)
  (heap-set! 3 #f)
  (heap-set! 4 'flat)
  (heap-set! 5 8)
  (heap-set! 6 'flat)
  (heap-set! 7 8)
  (for ([i (in-range 8 (heap-size))])
    (heap-set! i 'free)))

(define (queue-header) (heap-ref 5))
(define (queue-tail) (heap-ref 7))
(define (alloc-pointer) (+ 8 (heap-ref 1)))


;; find-free-space : loc number -> loc or #f
;; start must be a valid pointer
;; (not to the middle of an object)
(define (find-free-space start size)
(if (equal? (heap-ref 3) #t)
  (cond
    [(= start (heap-size)) #f]
    [else
     (case (heap-ref start)
       [(free)
        (if (n-free-blocks? start size)
            start
            (find-free-space (+ start 1) size))]
       [(flat) (find-free-space (+ start 2) size )]
       [(pair) (find-free-space (+ start 3) size )]
       [(proc)
        (find-free-space (+ start 3 (heap-ref (+ start 2)))
                         size )]
       [else
        (error 'find-free-space "cannot find free space at ~s" (heap-ref start))])])
    (cond
    [(= start (+ 8 (/ (- (heap-size) 8 ) 2))) #f]
    [else
     (case (heap-ref start)
       [(free)
        (if (n-free-blocks? start size)
            start
            (find-free-space (+ start 1) size))]
       [(flat) (find-free-space (+ start 2) size )]
       [(pair) (find-free-space (+ start 3) size )]
       [(proc)
        (find-free-space (+ start 3 (heap-ref (+ start 2)))
                         size )]
       [else
        (error 'find-free-space "cannot find free space at ~s" start)])])
    ))

;; n-free-blocks? : location? nat -> boolean?
(define (n-free-blocks? start size)
  (cond
    [(= size 0) #t]
    [(= start (if (heap-ref 3)
                  (heap-size)
                  (+ 8 (/ (- (heap-size) 8 ) 2)))) #f]
    [else
     (and (eq? 'free (heap-ref start))
          (n-free-blocks? (+ start 1) (- size 1)))]))

;; two space 
;; alloc : number[size] roots roots -> loc
(define (alloc n some-roots some-more-roots)
  (let ([next (find-free-space  (heap-ref 1) n )])
    (cond
      [next 
       
      ; (heap-set! 1 (+ n (heap-ref 1)))
       (printf "going to alloc ~s\n" (heap-ref 1))
       next
        ]
    
      [else
       
       (collect-garbage some-roots some-more-roots)
       (printf "requested size ~s\n" n)
       (let ([next (find-free-space  (heap-ref 1) n )])
         (unless next
           (error 'alloc "out of space"))
         ;(heap-set! 1 (+ n (heap-ref 1)))
         (printf "going to alloc after gc ~s\n" (heap-ref 1))
         (printf "going to alloc after gc, head ~s\n" (heap-ref 5))
         (printf "going to alloc after gc, tail ~s\n" (heap-ref 7))
         next)])))

;; collect-garbage : roots roots -> void?
(define (collect-garbage some-roots some-more-roots)
  (printf "collecting garbage\n")
  (validate-heap)
  
  (swap-heap)
 
  (traverse/roots (get-root-set))
  (traverse/roots some-roots)
  (traverse/roots some-more-roots)
  (traverse/pointers)

  (free-from-space))

(define (swap-heap)
  (case (heap-ref 3) 
      ; to-space should be in higher space
      [(#f) 
      
       (heap-set! 3 #t)
       (heap-set! 5 (+ 8 (/ (- (heap-size) 8) 2)))
       (heap-set! 7 (+ 8 (/ (- (heap-size) 8) 2)))
       ]
      
      ;to-space should be in lower space
      [(#t)
      
       (heap-set! 3 #f)
       (heap-set! 5 8)
       (heap-set! 7 8)
       ]))
;; validate-heap : -> void?
(define (validate-heap)
  (define (valid-pointer? i)
    (unless (memq (heap-ref i) '(flat pair proc free))
      (error 'validate-heap "found bad pointer @ ~s" i)))
  (let loop ([i 0])
    (when (< i (heap-size))
      (case (heap-ref i)
        [(flat)
         (loop (+ i 2))]
        [(pair)
         (valid-pointer? (heap-ref (+ i 1)))
         (valid-pointer? (heap-ref (+ i 2)))
         (loop (+ i 3))]
        [(proc)
         (for ([x (in-range 0 (heap-ref (+ i 2)))])
           (valid-pointer? (heap-ref (+ i 3 x))))
         (loop (+ i 3 (heap-ref (+ i 2))))]
        [(free)
         (loop (+ i 1))]
        [else (error 'validate-heap "corruption! @ ~a" i)]))))

(define (traverse/pointers)
  (do()
    ((= (heap-ref 5) (heap-ref 7))) 
    (move-head)))


(define (move-head)
  (let ([loc (heap-ref 5)])
    (printf "head ~s\n" (heap-ref 5))
    (printf "tail ~s\n" (heap-ref 7))
  (case (heap-ref loc)
    [(pair)
     (printf "moving head on pair\n")
     
     ;; read-root ?
     (heap-set! 6 (heap-ref 7))
     (move-tail (heap-ref (+ loc 1)))
     (heap-set! (+ 1 loc)  (heap-ref 6))
     (heap-set! 6 'flat)
     
     (heap-set! 6 (heap-ref 7))
     (move-tail (heap-ref (+ loc 2)))
     (heap-set! (+ 2 loc)  (heap-ref 6))
     (heap-set! 6 'flat)
     
     (heap-set! 5 (+ 3 loc))
     ]
    
    [(flat)
     (printf "moving head on flat\n")
     (heap-set! 5 (+ 2 loc))]
    
    [(proc)
     (printf "moving head on proc\n")
     
     (let ([ptr-count (heap-ref (+ 2 loc))])
       (for ([i (in-range 0 ptr-count)])
         (heap-set! 6 (heap-ref 7))
         (move-tail (heap-ref (+ loc 3 i)))
         (heap-set! (+ 3 i loc)  (heap-ref 6))
         (heap-set! 6 'flat))
       
       (heap-set! 5 (+ 3 ptr-count loc)))]
    [else 
     error 'move-head "undefined type"])))
  


(define (free-from-space)
   (case (heap-ref 3)
     [(#f)
       (heap-set! 1 (heap-ref 5))
       ;(printf "alloc pointer ~s\n" (heap-ref 1))
       (for ([i (in-range  (+ 8 (/ (- (heap-size) 8) 2))  (heap-size))])
         (heap-set! i 'free))]
     [(#t)
      (heap-set! 1 (heap-ref 5))
      ;(printf "alloc pointer ~s\n" (heap-ref 1))
       (for ([i (in-range  8 (+ 8 (/ (- (heap-size) 8) 2)))])
         (heap-set! i 'free))]))


;; traverse/roots : roots -> void
(define (traverse/roots thing)
  (cond
    [(empty? thing) (void)]
    [(list? thing) (for-each traverse/roots thing)]
    [(root? thing) (traverse/roots (read-root thing))]
                   
    [(number? thing) (move-tail thing)]))

;; traverse/loc : location -> void
(define (move-tail loc)
  (case (heap-ref loc)
    [(pair) 
     ;(heap-ref 7)
     (printf "moving tail ~s" (heap-ref loc))
     (heap-set! loc 'forw)
     (heap-set! (heap-ref 7) 'pair)
     (heap-set! (+ (heap-ref 7) 1) (heap-ref (+ 1 loc)))
     (heap-set! (+ (heap-ref 7) 2) (heap-ref (+ 2 loc)))
     (heap-set! 7 (+ 3 (heap-ref 7)))]
    
    [(flat) 
     ;(heap-ref 7)
     (heap-set! loc 'forw)
     (heap-set! (heap-ref 7) 'flat)
     (heap-set! (+ (heap-ref 7) 1) (heap-ref (+ 1 loc)))
     (heap-set! 7 (+ 2 (heap-ref 7)))]
    
    [(proc) 
     ;(heap-ref 7)
     (printf "moving proc @ ~s"  loc)
     (heap-set! loc 'forw)
     (heap-set! (heap-ref 7) 'proc)
     (heap-set! (+ (heap-ref 7) 1) (heap-ref (+ 1 loc)))
     (heap-set! (+ (heap-ref 7) 2) (heap-ref (+ 2 loc)))
     (for ([x (in-range 0 (heap-ref (+ 2 loc)))])
       (heap-set! (+ (heap-ref 7) 3 x) (heap-ref (+ loc 3 x)))
       ;(traverse/roots (heap-ref (+ loc 3 x)))
       )
     (heap-set! 7 (+ 3 (heap-ref (+ 2 loc)) (heap-ref 7)))]
    
    [else
     (error 'move-tail "crash ~s" (heap-ref loc))]))




(print-only-errors)
(test (let ([hp (make-vector 32)])
          (with-heap hp
                     (init-allocator)
                     (gc:alloc-flat 5)
                     hp
                     )) ;; return the heap!
        #(flat 10 flat #f flat 8 flat 8 
               flat 5 free free free free free free free free free free 
               free free free free free free free free free free free free))

(test (let ([hp (make-vector 32)])
          (with-heap hp
                     (init-allocator)
                     (gc:alloc-flat 2)
                     (gc:cons  5 6)
                     hp)) ;; return the heap!
        #(flat 13 flat #f flat 8 flat 8 flat 2 pair 5 6 free free
               free free free free free free free free free free free free free free free free free))
(test (let ([hp (make-vector 32)])
          (with-heap hp
                     (init-allocator)
                     (gc:cons 5 6 )
                     (gc:cons 7 8)
                     hp)) ;; return the heap!
        #(flat 14 flat #f flat 8 flat 8 pair 5 6 pair 7 8 
               free free free free free free free free free free free 
               free free free free free free free))

;(test (with-heap (make-vector 100)
;                 (init-allocator)
;                 (define f1 (gc:alloc-flat 1))
;                 (define r1 (make-root 'f1
;                                       (lambda () f1)
;                                       (lambda (v) (set! f1 v))))
;                 (define c1 (gc:cons r1 r1))
;                 (with-roots (c1)
;                             (gc:deref
;                              (gc:first
;                               (gc:cons r1 r1)))))
;      1)


(test/exn (with-heap 
       (make-vector 16 #f) 
       (init-allocator)
       (gc:alloc-flat 111)
       (gc:set-first! 12 7)) "non pair")
(test (let ([hp (make-vector 20)])
          (with-heap hp
                     (init-allocator)
                     (free-from-space)
                     hp)) ;; return the heap!
       #(flat 8 flat #f flat 8 flat 8 free free free free free free free free free free free free))

;(test (let ([hp (make-vector 20)])
;          (with-heap hp
;                     (init-allocator)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                     (gc:alloc-flat 3)
;                    
;                     hp)) ;; return the heap!
;          #(flat 14 flat #t flat 14 flat 14 
;                 free free free free free free 
;                 flat 3 free free free free) )

(test (with-heap 
       (make-vector 16 #f) 
       (init-allocator)
       (gc:alloc-flat 111)
       (gc:deref 8)) 111)

(test (with-heap 
       (make-vector 16 #f) 
       (init-allocator)
       (gc:alloc-flat 111)
       (gc:flat? 8)) #t)

(test (with-heap 
       (make-vector 16 #f) 
       (init-allocator)
       (gc:alloc-flat 111)
       (gc:cons? 8)) #f)

(test (with-heap 
       (make-vector 18 #f) 
       (init-allocator)
       (gc:cons 4 5)
       (gc:flat? 8)) #f)

(test (with-heap 
       (make-vector 18 #f) 
       (init-allocator)
       (gc:cons 4 5)
       (gc:cons? 8)) #t)

(test (let ([hp (make-vector 40 )])
        (with-heap hp
                   (init-allocator)
                   (gc:alloc-flat 42) ; 8 -> DEAD
                   (gc:alloc-flat 54) ; 10 -> DEAD
                   (gc:alloc-flat 66) ; 12 -> DEAD
                   (gc:cons 10 12)    ; 14 -> DEAD
                   (gc:alloc-flat 78) ; 17 -> DEAD
                   (gc:cons 10 12)     ; 19 -> DEAD
                   (gc:cons 10 12)      ; 22
                   (gc:cons 10 12)     ;25
                   (gc:cons 10 12)
                   (gc:cons 10 12)
                   (gc:alloc-flat 99) ; The guy that triggers the gc)
        hp))
      #(flat 10 flat #f flat 8 flat 8 
             flat 99 free free free free free free free free free free free free free free
             free free free free free free free free free free free free free free free free))
      ;(vector 26 28 26 '() #f #t 0 1 2 3 4 5
       ;       ; space 1
        ;      'freed 'freed 'freed 'freed 'freed 'freed 'freed
         ;     'freed 'freed 'freed 'freed 'freed 'freed 'freed
              ; space 2
          ;    'flat 99 'free 'free 'free 'free 'free
           ;   'free 'free 'free 'free 'free 'free 'free))
(test (let ([h (make-vector 40 #f)])
        (with-heap h
                   (init-allocator)
                   (gc:alloc-flat 42) ; 8 -> DEAD
                   (gc:alloc-flat 54) ; 10 -> 28
                   (gc:alloc-flat 66) ; 12 -> 26
                   (gc:cons 12 8)    ; 14 -> DEAD
                   (gc:alloc-flat 78) ; 17 -> DEAD
                   (gc:cons 10 17)    ; 19 -> DEAD
                   (gc:cons 12 10)    ; The guy that triggers the first gc. 26 -> 8
                   (gc:alloc-flat 78) ; 29 -> DEAD 
                   (gc:alloc-flat 78) ; 31 -> DEAD
                   (gc:alloc-flat 78) ; 33 -> DEAD
                   ; this guy triggers the second gc.
                   ; he references the cons that triggered the first gc
                   ; and an immediate.
                   (gc:cons 31 33 ) ; ? 
        h))
      #(flat 40 flat #t flat 28 flat 28 
             free free free free free free free free free free free free free free free free
             flat 66 flat 54 pair 12 10 flat 78 flat 78 flat 78 pair 31 33)
      )