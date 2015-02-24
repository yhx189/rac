#lang plai

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


(define-type RFAE
  [num (n number?)]
  [add (lhs RFAE?) (rhs RFAE?)]
  [sub (lhs RFAE?) (rhs RFAE?)]
  [id (name symbol?)]
  [fun (param symbol?) (body RFAE?)]
  [app (fun RFAE?) (arg RFAE?)]
  [seqn (a RFAE?) (b RFAE?)]
  [record-struct (fields (listof symbol?))
                 (exprs (listof RFAE?))]
  [record-get (body RFAE?) (r symbol?)]
  [record-set (bx-expr RFAE?) (r symbol?) (val-expr RFAE?)])

;garbage collection
;tail recursion

(define-type RFAE-Value
  [numV (n number?)]
  [closureV (param symbol?)
            (body RFAE?)
            (ds DefrdSub?)]
  [boxV (addr integer?)] )

(define-type field-pair
  [aPair (field symbol?)
         (value RFAE-Value?)])

(define-type Store
  [mtSto]
  [aSto (addr integer?)
        (field-value-pairs 
         (listof field-pair?))
        (rest Store?)])
(define (find-and-set field val pairs)
  (if (empty? pairs)
      (error 'interp-expr "unknown field")
      (if (symbol=? field (aPair-field (first pairs)))
          
          (append (list (aPair field val))
                  (rest pairs))
          (append (list (first pairs)) 
                  (find-and-set field val (rest pairs))))))

(define (store-set address val field st)
  (type-case Store st
    [mtSto () (error 'interp-expr "unknown field")]
    [aSto (addr field-pairs rest-st)
          (if (equal? addr address)
              (aSto addr (find-and-set field val field-pairs) rest-st)
              (aSto addr field-pairs (store-set address val field rest-st)))]))

(define (store-lookup address field st)
  (type-case Store st
    [mtSto () (error 'interp-expr "unknown field ~s" field)]
    [aSto (addr field-pairs rest-st)
          (if (equal? addr address)
              (find field field-pairs)
              (store-lookup address field rest-st))]))

(define (find field field-pairs)
  (if (empty? field-pairs)
      (error 'interp-expr "unknown field ~s" field)
      (if (symbol=? field (aPair-field (first field-pairs)))
          (aPair-value (first field-pairs))
          (find field (rest field-pairs)))))


(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (n v st1)
          (max n (max-address st1))]))

(define-type Value*Store
  [v*s (value RFAE-Value?)
       (store Store?)])

(define-type DefrdSub
  [mtSub]
  [aSub (sub-name symbol?)
        (val RFAE-Value?)
        (rest-ds DefrdSub?)])

(define (lookup name ds st)
  (type-case DefrdSub ds
    [mtSub () (error 'lookup "free identifier ~s" name)]
    [aSub (sub-name val rest-ds)
          (if (symbol=? sub-name name)
              (v*s val st)
              (lookup name rest-ds st))]))

(define (num-op op)
  (lambda (x y)
    (numV (op (numV-n x) (numV-n y)))))
(define num+ (num-op +))
(define num- (num-op -))

(define (interp-expr a-rfae)
  (type-case Value*Store (interp a-rfae (mtSub) (mtSto))
    [v*s (val st)
         (type-case RFAE-Value val
           [numV (n)  n]
           [closureV (param body ds) 'procedure]
           [boxV (addr) 'struct])]))



;; size : any -> number
;; computes a (very rough!) approximate to
;; the size a PLAI object takes in memory
(define (size s)
  (cond
    [(struct? s)
     (size (struct->vector s))]
    [(vector? s)
     (for/fold ([tot 0])
               ([ele (in-vector s)])
       (+ tot (size ele)))]
    [(pair? s)
     (+ 1 (size (car s)) (size (cdr s)))]
    [else 1]))
(define (list-max ll)
  (if (empty? ll)
      0
      (if (> (first ll) (list-max (rest ll)))
          (first ll)
          (list-max (rest ll)))))

(define/contract (interp a-rfae ds st)
  (-> RFAE? DefrdSub? Store? Value*Store?)
  ;(printf "size ~s\n" (size st))
  (type-case RFAE a-rfae
    [num (n) (v*s (numV n) st)]
    [add (l r)
         (type-case Value*Store (interp l ds st)
           [v*s (l-val l-st)
                (type-case RFAE-Value l-val
                  [numV (ln) 
                        (type-case Value*Store (interp r ds l-st)
                          [v*s (r-val r-st)
                               (type-case RFAE-Value r-val
                                 [numV (rn) (v*s 
                                             (num+ l-val r-val)
                                             r-st)]
                                 [else
                                  (error 'interp-expr "numeric operation expected number")])])]
                  [else (error 'interp-expr "numeric operation expected number")])])]
    [sub (l r)
         (type-case Value*Store (interp l ds st)
           [v*s (l-val l-st)
                (type-case RFAE-Value l-val
                  [numV (ln) 
                        (type-case Value*Store (interp r ds l-st)
                          [v*s (r-val r-st)
                               (type-case RFAE-Value r-val
                                 [numV (rn) (v*s 
                                             (num- l-val r-val)
                                             r-st)]
                                 [else
                                  (error 'interp-expr "numeric operation expected number")])])]
                  [else (error 'interp-expr "numeric operation expected number")])])]
    
    [id (name) 
        (lookup name ds st)]
    [fun (param body-expr) 
         (v*s
          (closureV param body-expr ds)
          st)]
    [seqn (a b)
          (type-case Value*Store (interp a ds st)
            [v*s (val1 st1)
                 (type-case Value*Store (interp b ds st1)
                   [v*s (val2 st2)
                        (v*s val2 st2)])])]
    
    [record-struct (fields exprs) ;; now fields and exprs are both lists
                   (local [(define (look-for-st addr expr st)
                        (type-case Value*Store (interp expr ds st)
                               [v*s (val st1)
                                    (type-case Store st1
                                      [mtSto () (mtSto)]
                                      [aSto (addr1 v1 st2)
                                            (if (equal? (aSto-addr st1) addr)
                                                st1
                                                (look-for-st addr st2))])])
                             )]
                   (local [(define (record-struct-helper field expr )
                               (type-case Value*Store (interp expr ds st)
                                 [v*s (val st1)
                                      (aPair field val) ]))]
                       (local [(define (find-max-addr field expr)
                                 (type-case Value*Store (interp expr ds st)
                                   [v*s (val st1)
                                        (max-address st1)]))]
                         (local [(define (find-max-ref  i)
                                       (if (equal? (find-max-addr (list-ref fields i)
                                                                  (list-ref exprs i)) 
                                                   (list-max (map (lambda (field expr)
                                                                    (find-max-addr field expr ))
                                                                  fields exprs )))
                                           i
                                           (find-max-ref  (+ i 1))
                                           ))]
                           (if (empty? exprs)
                               (v*s (boxV (+ 1 (list-max (map (lambda (field expr)
                                                            (find-max-addr field expr ))
                                                          fields exprs ))))
                                    (aSto (+ 1 (list-max (map (lambda (field expr)
                                                            (find-max-addr field expr ))
                                                          fields exprs )))
                                          empty
                                          st))
                           (v*s (boxV (+ 1 (list-max (map (lambda (field expr)
                                                            (find-max-addr field expr ))
                                                          fields exprs ))))
                                (aSto (+ 1 (list-max (map (lambda (field expr)
                                                            (find-max-addr field expr ))
                                                          fields exprs )))
                                      (map (lambda (field expr)
                                             (record-struct-helper field expr ))
                                           fields exprs )
                                      (look-for-st (list-max (map (lambda (field expr)
                                                                    (find-max-addr field expr ))
                                                                  fields exprs )) 
                                                   (list-ref exprs (find-max-ref 0))
                                                   st))))))))]
    
    [record-get (bx-expr f)
                (type-case Value*Store (interp bx-expr ds st)
                  [v*s (bx-val sub-st)
                       (type-case RFAE-Value bx-val
                         [boxV (bbx-val)
                               (v*s 
                                (store-lookup bbx-val f sub-st)
                                sub-st)]
                         [else (error 'interp-expr "record operation expected record")])])]
    
    [record-set (bx-expr f val-expr)
                (type-case Value*Store (interp bx-expr ds st)
                  [v*s (bx-val st1)
                       (type-case RFAE-Value bx-val
                         [boxV (bbx-val)
                               (type-case Value*Store (interp val-expr ds st1)
                                 [v*s (val-val st2)
                                      (v*s 
                                       (store-lookup bbx-val f st1)
                                       (store-set 
                                        bbx-val
                                        val-val
                                        f
                                        st1))])]
                         [else (error 'interp-expr "record operation expected record")])])]
    
    [app (fun-expr arg-expr)
         (type-case Value*Store  (interp fun-expr ds st)
           [v*s (val1 st1)
                (type-case RFAE-Value val1                 
                  [closureV (fun-v-param fun-v-body fun-v-ds)
                            (type-case Value*Store  (interp arg-expr ds st1)
                              [v*s (val2 st2)
                               (interp fun-v-body
                                           (aSub fun-v-param
                                                 val2
                                                 fun-v-ds)
                                           st2)])]
                  [else (error 'interp-expr "application expected procedure")])])]))



(define (parse sexps)
  ;(-> sexpr  RFAE?)
  ; parse '{} -> RFAE 
  (cond 
    [(number? sexps) (num sexps)]
    [(symbol? sexps) (id sexps)]
    [(list? sexps) (cond 
                     
                     [(equal?  (first sexps) '+) (add (parse (second sexps))  (parse (third sexps)))]
                     [(equal?  (first sexps) '-) (sub (parse (second sexps))  (parse (third sexps)))]
                     [(equal?  (first sexps) 'with) (app
                                                     (fun (first (second sexps)) (parse (third sexps)))
                                                     (parse (second (second sexps))))]
                     
                     
                     [(equal? (first sexps) 'get) (record-get
                                                   (parse (second sexps))
                                                   (third sexps))]
                     [(equal? (first sexps) 'set) (record-set
                                                   (parse (first (rest sexps)))
                                                   (second (rest sexps))
                                                   (parse (third (rest sexps))))]
                     [(equal? (first sexps) 'seqn) (seqn
                                                    (parse (second sexps))
                                                    (parse (third sexps)))]
                     [(equal? (first sexps) 'fun)(case (length (second sexps))
                                                   [(1) (fun 
                                                         (first (second sexps)) 
                                                         (parse (third sexps)))]
                                                   [else ; we dont have multiple arity functions actually
                                                    (fun
                                                     (first (second sexps))
                                                     (parse (list
                                                             (first sexps)
                                                             (rest (second sexps))
                                                             (third sexps))))])]  
                     [(equal? (first sexps) 'struct) 
                      (record-struct
                       (map (lambda (x)
                              (first x))
                            (rest sexps))
                       (map (lambda (x)
                              (parse (rest x)))
                            (rest sexps)))]
                     
                     [else
                      (case (length sexps)
                        [(1)  (parse (first sexps))]
                        
                        [else  (app
                                (parse (drop-right sexps 1))
                                (parse (last sexps))
                                )])])]))




(print-only-errors)
(test (interp-expr (parse '{get {struct {x 1}{y {{fun {b}{+ b 3}} 4}}} y}))
      7)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   
                                                   {seqn
                                                    {{s r1} {g r2}}
                                                    
                                                    {get r2 b}}
                                                   }}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      4)

(test (interp-expr (parse '{struct {x {struct {y {struct {z 1}}}}}}))
      'struct)
(test (interp-expr (parse `{with {b {struct {x 2} {y 1}}} 
                                  
                                       {get b x}})) 2)

(test/exn (interp-expr (parse `{with {b {struct {x 2} {y 1}}} 
                                 {seqn {seqn {set b x 3} {get b x}} 
                                       {get c x}}})) 
          "free identifier")
(test (interp-expr (parse `{with {b {struct {x 2} {y {struct {z 3}}}}} 
                                 {seqn {seqn {set b x 3} {get b x}} 
                                       {get b y}}}))
             'struct)

(test (interp-expr (parse `{with {b {struct {x 2} {y 1}}} 
                                 {seqn {seqn {set b x 3} {get b x}} 
                                       {get b x}}})) 3)
(test (interp-expr (parse `{get {struct {y 3}
                                  {z {struct {y 4}}}}
                                
                                z}))
      'struct)
(test (interp-expr (parse `{get {get {struct {y 3}
                                       {z {struct {y 4}}}}
                                     z}
                                y}))
      4)
;(test/exn (interp-expr (parse `{struct {b {struct {x 1}} {c {get b x}}}} ))
;          "free identifier")
(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")

(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  
                                  {get r x}
                                  {set r x 5}}}
                            {struct {x 1}}}))
      1)
(test/exn (interp-expr (parse '{{fun {f} {+ x 1}} 3}))
          "free identifier")
(test/exn (interp-expr (parse '{get {struct {x 1} {y 2} {z 3}} c }))
          "unknown field")

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {seqn
                                   {set r x 6}
                                   {get r x}}}}
                            {struct {x 1}}}))
      6)
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {seqn
                                   
                                   {get r x}
                                   {set r x 6}}}}
                            {struct {x 1}}}))
      5)
(test (interp-expr (parse `{set {struct {x 42}} x 2}))
      42)
(test/exn (interp-expr (parse `{set {struct} x 2}))
          "unknown field")

(test/exn (interp-expr (parse `{get 1 a}))
          "record operation expected record")
(test/exn (interp-expr (parse `{get {fun {a} a} a})) 
          "record operation expected record")

(test (interp-expr (parse `{set {get {struct {r {struct {z 0}}}} r} z 1}))
      0)

(test/exn (interp-expr (parse '{get {set {struct {r {struct {z 0}}}} z 1} r}))
          "unknown field") 


(test (interp-expr (parse `{- {set {struct {x 42}} x 2}
                              {set {struct {x 3}} x 2}}))
      39)
(test (interp-expr (parse `{get {struct {x {set {struct {x 42}} x 2}}}
                                x}))
      42)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   
                                                   {seqn
                                                    
                                                    {{s r1} {g r2}}
                                                    {get r1 b}
                                                    
                                                    }}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      3)
(test (interp-expr (parse '{seqn
                            {set  {struct {a 0} {b 2}}  b {get  {struct {a 3} {b 4}} a}}
                            {get  {struct {a 0} {b 2}}  b}}))
      
      
      2)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   
                                                   
                                                   {get r2 b}
                                                   
                                                   
                                                   }}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      4)
(test (interp-expr (parse '{{{fun {s} 
                                  {fun {r1}
                                       {{s r1} 3}}} {fun {r} {fun {v} {set r b v}}}}
                            {struct {a 0} {b 2}}}))
      2)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   
                                                   {seqn
                                                    {{s r1} {g r2}}
                                                    {+ {seqn
                                                        {{s r2} {g r1}}
                                                        {get r1 b}}
                                                       0}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      3)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              
                                              {get r1 b}}}}
                               
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}}             ; r1
                          ))            
      2)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {get r1 b}}}}}
                               
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      2)

(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ {get r1 b}
                                                      {seqn
                                                       {{s r1} {g r2}}
                                                       {+ {seqn
                                                           {{s r2} {g r1}}
                                                           {get r1 b}}
                                                          {get r2 b}}}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      5)
(test (interp-expr (parse '{{{{{fun {g}
                                    {fun {s}
                                         {fun {r1}
                                              {fun {r2}
                                                   {+ 
                                                    {seqn
                                                     {{s r1} {g r2}}
                                                     {+ {seqn
                                                         {{s r2} {g r1}}
                                                         {get r1 b}}
                                                        {get r2 b}}}
                                                    {get r1 b}}}}}}
                               {fun {r} {get r a}}}            ; g
                              {fun {r} {fun {v} {set r b v}}}} ; s
                             {struct {a 0} {b 2}}}             ; r1
                            {struct {a 3} {b 4}}}))            ; r2
      6)
;(test (interp-expr (parse `{with {b {struct {x 1}}}
;                                 {with {f {fun {f}
;                                               {seqn {set b x 2}
;                                                     {f f}}}}
;                                       {f f}}}))
;      5) 