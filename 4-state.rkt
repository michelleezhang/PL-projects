#lang plai

(print-only-errors)

; SFAE language
(define-type SFAE
  [num (n number?)]
  [id (name symbol?)]
  [add (lhs SFAE?) (rhs SFAE?)]
  [sub (lhs SFAE?) (rhs SFAE?)]
  [fun (param-name symbol?) (body SFAE?)] ; create fun (param) body
  [app (fun-exp SFAE?) (arg-exp SFAE?)] ; execute fun-exp with arg-exp
  [my-struct (field-value (listof (cons/c symbol? SFAE?)))] ; listof cons (symbol, FAE)
  [get (a-struct SFAE?) (field symbol?)] ; for struct ada(name: me, value: mo), (get ada name) returns me
  [my-set (a-struct SFAE?) (field symbol?) (value SFAE?)] ; so (set ada name moi) should return me, and update (name: moi) in ada
  [seqn (expr1 SFAE?) (expr2 SFAE?)]) ; opens stuff one at a time

; this data type is either an "empty" sub or it's like a list of subs (each with a name and value)
(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value SFAE-Value?) ; changed to accept an FAE
        (rest DefSub?)])

; either num or closure or struct
(define-type SFAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body SFAE?)
            (ds DefSub?)]
  [structV (address number?)
           (fields-pointers (listof (cons/c symbol? number?)))])

; store value, represents memory 
(define-type Store
  [mtSto]
  [aSto (address integer?)
        (value SFAE-Value?)   
        (rest Store?)])

; new return type for interp
(define-type Value*Store
  [v*s (v SFAE-Value?)
       (s Store?)])

; parse: s-exp -> SFAE
(define (parse s-exp)
  (cond
    [(number? s-exp)
     (num s-exp)]
    [(symbol? s-exp)
     (id s-exp)]
    [(list? s-exp)
     (when (empty? s-exp)
       (error 'parse "the empty list is not a valid SFAE"))
     (case (first s-exp)
       [(+)
        (check-pieces s-exp "add" 3)
        (add (parse (second s-exp))
             (parse (third s-exp)))]
       [(-)
        (check-pieces s-exp "sub" 3)
        (sub (parse (second s-exp))
             (parse (third s-exp)))]
       [(fun)
        (check-pieces s-exp "fun" 3)
        (check-pieces (second s-exp) "parameter" 1)
        (fun (first (second s-exp)) ; (second s-exp) is a list, so call first to access the actual item
             (parse (third s-exp)))]
       [(struct)
        ; note empty struct is ok
        (cond
          [(equal? (length s-exp) 1) ; the way they're representing empty structs is (struct)
           (my-struct `())]
          [(empty? (second s-exp))
           (my-struct `())]
          [else
           ; check that the field names are distinct
           (define fields (map (lambda (x) (first x)) (cdr s-exp))) ; create a list of field namse
           (unless (equal? (length fields) (length (remove-duplicates fields))) ; check for duplicates
             (error 'parse "fields must be distinct!"))
           ; create a struct
           (define fv-pairs (map (lambda (x) (cons (first x) (parse (second x)))) (cdr s-exp))) ; create a list of the field-value pairs, with the second argument parsed
           (my-struct fv-pairs)])]
       [(get)
        (check-pieces s-exp "get" 3)
        (get (parse (second s-exp))
             (third s-exp))] ; from contract, first arg is SFAE, second is a symbol (so don't parse)
       [(set)
        (check-pieces s-exp "set" 4)
        (my-set (parse (second s-exp))
                (third s-exp)
                (parse (fourth s-exp)))]
       [(seqn)
        (check-pieces s-exp "seqn" 3)
        (seqn (parse (second s-exp))
              (parse (third s-exp)))]
       [else
        (check-pieces s-exp "app" 2)
        (app (parse (first s-exp))
             (parse (second s-exp)))])] ; app or error
    [else
     (error 'parse "expected SFAE, got ~a" s-exp)]))

(define (check-pieces s-exp expected n-pieces)
  (unless (and (list? s-exp)
               (= n-pieces (length s-exp)))
    (error 'parse "expected ~a got ~a" expected s-exp)))


;; parse tests
(test (parse `1) (num 1))
(test (parse `{struct {x 1}})
      (my-struct (list (cons 'x (num 1)))))
(test (parse `{struct {x 1} {y 2}})
      (my-struct (list (cons 'x (num 1)) (cons 'y (num 2)))))
(test (parse `{struct {x 1} {y 2} {z 3}})
      (my-struct (list (cons 'x (num 1)) (cons 'y (num 2)) (cons 'z (num 3)))))
(test (parse `{struct {}})
      (my-struct '()))
(test (parse '{{fun {r}
              {get r x}}
         {struct {x 1}}})
      (app (fun 'r (get (id 'r) 'x)) (my-struct (list (cons 'x (num 1))))))
(test (parse '{{fun {r} {seqn {set r x 5} {get r x}}}
         {struct {x 1}}})
      (app (fun 'r (seqn (my-set (id 'r) 'x (num 5)) (get (id 'r) 'x))) (my-struct (list (cons 'x (num 1))))))
(test (app (fun 'r (seqn (my-set (id 'r) 'x (num 5)) (get (id 'r) 'x)))
     (my-struct (list (cons 'x (num 1)))))
      (app (fun 'r (seqn (my-set (id 'r) 'x (num 5)) (get (id 'r) 'x))) (my-struct (list (cons 'x (num 1))))))

; interp : SFAE? DefSub? Store? -> Value*Store?
(define (interp a-sfae ds st)
  (type-case SFAE a-sfae
    [num (n) (v*s (numV n) st)]
    [id (name) (v*s (lookup name ds) st)]
    [add (lhs rhs) (numop + lhs rhs ds st)]
    [sub (lhs rhs) (numop - lhs rhs ds st)]
    [fun (param-name body)
         (v*s (closureV param-name body ds) st)]
    [app (fun-exp arg-exp)
         (interp-two fun-exp arg-exp ds st
                     (lambda (fun-val arg-val st3)
                       (type-case SFAE-Value fun-val
                         [closureV (param-name body closed-ds)
                                   (interp body
                                           (aSub param-name
                                                 arg-val
                                                 closed-ds)
                                           st3)]
                         [else (error 'interp "expected function, got ~s" fun-val)])))]
    [my-struct (field-value)
               ; a spot in the store holds either a struct (a list of field names and corresponding pointers) or a field value
               ; in other words...
               ; structs: hold field names and corresponding pointers
               ; the store maps pointers to values

               ; this is a recursive helper
               ; we go through each of the fv-pairs and for each one:
               ;        assign an address (pointer) and place the value at that address
               ;        add the name of the field and corresponding pointer to a list
               ; at the end, allocate a spot for the "struct" (aka the list of field names and pointers)

             ;  (define struct-add (malloc store))
              ; (define fields (map ) ; get symbols from fields-valuse
               ; recurse interp -- get field addresses and store

               ; here, we call our recursive helper
               (mystruct-interp-helper field-value `() st ds)]

    [get (a-struct field)
         (type-case Value*Store (interp a-struct ds st)
           [v*s (address st2)
                ; here, we interpret the struct
                ; the address we get back is the address of the struct
                ; we need to go to that address and then lookup the field we want in the field-pointers list
                ; then follow that pointer to get the value we want to return

                ; make sure that what we got is in fact a struct
                (cond
                  [(structV? address)
                   ; here, we get the address of the interpreted struct
                   (define struct-in-store (lookup-store (structV-address address) st2))
                   
                   ; here, we just make a variable for the fields-pointers list in that struct
                   (define curr-fps (structV-fields-pointers struct-in-store))
                   
                   ; lookup the value :)
                   (define (lookup-value name list)
                     (cond [(empty? list)
                            (error "unknown field")]
                           [else
                            (define curr (first list))
                            [cond [(equal? name (car curr))
                                   (lookup-store (cdr curr) st2)]
                                  [else
                                   (lookup-value name (cdr list))]]]))

                   ; return our v*s
                   (v*s (lookup-value field curr-fps) st2)]
                  [else (error "expected struct, got ~a:" a-struct)])])]


    [my-set (a-struct field value)
            (type-case Value*Store (interp a-struct ds st) ; first, we put the struct in store
              [v*s (address st2)

                   ; check that it is a struct
                   (cond
                     [(structV? address)
                      (define struct-in-store (lookup-store (structV-address address) st2)) ; lookup the struct

                      (define curr-fps (structV-fields-pointers struct-in-store))

                      ; the list of (fields -> pointers) held in the struct
                      (define (set-value name list)
                        (cond [(empty? list) (error "unknown field")]
                              [else
                               (define curr (first list))
                               [cond [(equal? name (car curr))
                                      ; so now curr is the field-pointer mapping of the field we want
                                      (define val-address (cdr curr))

                                      ; CANNOT assume that value is a number -- it is an SFAE -> we need to interpret it to get it in SFAE-Value form
                                      (define value-interped (interp value ds st2))

                                      ; now we have interped the value, so our new store is (v*s-s value-interped)
                                      ; and the value we want to insert is (v*s-s value-interped), in place of something else
                                      ; now what we need to do is create a new store (we basically need to rebuild the original store
                                      ; up until the point where we want to replace, then we just swap it out and attach the rest of the store

                                      (define (modify-store curr-address store)
                                        (cond [(< curr-address 1)
                                               (error "unknown field")]
                                              [(equal? (aSto-address store) val-address)
                                               ; this changes the value we want to change, then strings along the rest of the store without changing it!

                                               (aSto val-address (v*s-v value-interped) (aSto-rest store))]

                                              [else
                                               ; this adds the stuff at the start of the store and recurses
                                               (aSto curr-address (lookup-store curr-address store) (modify-store (- curr-address 1) (aSto-rest store)))]))
                                      ; create our modified store
                                      (define new-store (modify-store (max-address (v*s-s value-interped)) (v*s-s value-interped)))
                                      (v*s (lookup-store (cdr curr) (v*s-s value-interped)) new-store)]
                                     [else
                                      (set-value name (cdr list))]]]))

                      ; here we actually call the function
                      (set-value field curr-fps)]
                     [else (error "expected struct, got ~a:" a-struct)])])]
    
    [seqn (expr1 expr2)
          (interp-two expr1 expr2 ds st
                      (lambda (v1 v2 st3)
                        (v*s v2 st3)))]))

(define (malloc st)
  (+ (max-address st) 1))

(define (max-address st)
  (type-case Store st
    [mtSto () 0]
    [aSto (a v r) (max a (max-address r))]))

(define (mystruct-interp-helper fields-values fields-pointers store ds)
  (cond [(empty? fields-values)
         ; allocate a spot for the struct
         (define struct-address (malloc store))
         ; return a Value*Store, which holds the names of all the fields-pointers and whatnot
         (v*s (structV struct-address fields-pointers)
              (aSto struct-address
                    (structV struct-address fields-pointers) ; structV holds fieldname-pointer pairs
                    store))]
        [else
         (define val-store (interp (cdr (first fields-values)) ds store))
         (define new-store (v*s-s val-store))
         
         ; allocate a spot for the current fv-pair
         
         (define val-address (malloc new-store))
         
         ; (first list) is the first fv-pair
         ; car gets the first item in the pair (aka the field name)
         ; we append the field-pointer pair to the fields-pointers list
         (define new-fields-pointers (append 
                                             (list (cons (car (first fields-values)) val-address)) fields-pointers))
                     
         
         ;(displayln "VAL")
        ; (displayln (malloc store))
         
         ; interp the value to get it as a numV

         ; this is where we recurse
        ; (displayln "NEW")
       ;  (displayln (aSto val-address (v*s-v val-store) (v*s-s val-store)))
         
         (mystruct-interp-helper (cdr fields-values)
                                 new-fields-pointers
                                 (aSto val-address (v*s-v val-store) (v*s-s val-store)) ds)]))

;(test (mystruct-interp-helper (list (cons 'a (num 1)) (cons 'b (num 2))) `() (mtSto) (mtSub)) (v*s (structV 3 (list (cons 'a 1) (cons 'b 2)))
;                                                                                       (aSto 3 (structV 3 (list (cons 'a 1) (cons 'b 2)))
;                                                                                             (aSto 2 (numV 2)
;                                                                                                   (aSto 1 (numV 1)
;                                                                                                         (mtSto))))))

(test (mystruct-interp-helper (list (cons 'y (my-struct (list (cons 'z (num 5)))))) `() (mtSto) (mtSub)) (v*s (structV 4 (list (cons 'y 3)))
                                                                                             (aSto 4 (structV 4 (list (cons 'y 3)))
                                                                                                   (aSto 3 (structV 2 (list (cons 'z 1)))
                                                                                                         (aSto 2 (structV 2 '((z . 1)))
                                                                                                               (aSto 1 (numV 5)
                                                                                                                     (mtSto)))))))



; interpret two things and call finish to do rest of work
(define (interp-two expr1 expr2 ds st finish)
  (type-case Value*Store (interp expr1 ds st)
    [v*s (v1 st2)
         (type-case Value*Store (interp expr2 ds st2)
           [v*s (v2 st3)
                (finish v1 v2 st3)])]))

(define (lookup-store a st)
  (type-case Store st
    [mtSto () (error 'interp "dangling pointer! ~a" a)]
    [aSto (a2 v r) (if (equal? a2 a)
                       v
                       (lookup-store a r))]))


;; numop : (number? number? -> number?) SFAE? SFAE? DefSub? Store? -> SFAE-Value?
(define (numop op l r ds st)
  (interp-two l r ds st
              (lambda (l-val r-val st3)
                (unless (numV? l-val)
                  (error 'interp "expected number, got ~a" l-val))
                (unless (numV? r-val)
                  (error 'interp "expected number, got ~a" r-val))
                (v*s (numV (op (numV-n l-val) (numV-n r-val)))
                     st3))))

;; lookup : symbol? DefSub? -> SFAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

; interp-expr: s-expression -> SFAE-Value?
(define (interp-expr s-exp)
  (type-case Value*Store (interp s-exp
                                 (mtSub)
                                 (mtSto))
    ; interpret the s-exp with the default ds and st and get the resulting v*s
    [v*s (v s)   
         ; return only the Value part
         (type-case SFAE-Value v
           [numV (n) ; if Value is a number, return the number
                 n]
           [closureV (param-name body ds) ; otherwise, return 'function
                     'function]
           [structV (address fields-pointers) ; or 'symbol
                   ; (displayln v)

                    ; what the function is supposed to do is
                    ; get (get r y) z, where r is (y: (struct z 5))
                    ; so (get r y) returns (struct z 5)
                    ; then we should get (struct z 5) z, so return 5
                    'struct])]))


; test cases

; get
(test (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            {struct {x 1}}}))
      1)

(test (interp-expr (parse '{{fun {r}
                                 {get r y}}
                            {struct {x 2} {y 1}}}))
      1)
(test (interp-expr (parse '{{fun {r}
                                 {get r a}}
                            {struct {x 2} {y 1} {z 300} {b 50} {c 19.0} {a 11} {lol 60}}}))
      11)

; set
(test (interp-expr (parse '{set {struct {x 42}} x 2}))
      42)
(test (interp-expr (parse '{set {struct {x 1} {y 42}} y 2}))
      42)
(test (interp-expr (parse '{set {struct {x 42} {y 5} {z 1231}} y 1}))
      5)

; set get
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r x}}}
                            {struct {x 1}}}))
      5)
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r y}}}
                            {struct {x 1} {y 2}}}))
      2)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r c 18}
                                  {get r c}}}
                            {struct {x 1} {y 2} {z 3} {a 4} {b 5} {c 6} {d 7}}}))
      18)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r d 18}
                                  {get r d}}}
                            {struct {x 1} {y 2} {z 3} {a 4} {b 5} {c 6} {d 7}}}))
      18)

; set set set get
(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                 {seqn
                                  {set r x 5}
                                  {set r x 6}}
                                 {get r x}}

                                 }
                            {struct {x 1}}}))
      6)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {seqn
                                  {set r c 5}
                                  {seqn
                                  {set r c 6}
                                  {seqn
                                  {set r c 7}
                                  {seqn
                                  {set r c 8}
                                  {set r c 1000}}}}}
                                 {get r c}}}
                            {struct {x 1} {y 2} {z 3} {a 4} {b 5} {c 6} {d 7}}}))
      1000)

(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {seqn
                                   {set r c 5}
                                   {seqn
                                    {set r c 6}
                                    {seqn
                                     {set r d -7.1}
                                     {seqn
                                      {set r c 8}
                                      {set r c 1000}}}}}
                                  {get r d}}}
                            {struct {x 1} {y 2} {z 3} {a 4} {b 5} {c 6} {d 7}}}))
      -7.1)


(test (interp-expr (parse '{{fun {r}
                                 {seqn
                                 {seqn
                                  {set r x 5}
                                  {set r x 6}}
                                 {get r y}}

                                 }
                            {struct {x 1} {y 2}}}))
      2)


; return struct
(test (interp-expr (parse '{struct {z {get {struct {z 0}} z}}})) 'struct)
(test (interp-expr (my-struct (list (cons 'x (num 1))))) 'struct)
(test (interp-expr (fun 'x (id 'x))) 'function)

; errors
(test/exn (interp-expr (parse '{struct {z {get {struct {z 0}} y}}}))
          "unknown field")
(test/exn (interp-expr (parse '{struct {z {get {struct} y}}}))
          "unknown field")
(test/exn (interp-expr (parse '{struct {z {set {struct {z 0}} y 2}}}))
          "unknown field")
(test/exn (interp-expr (parse '{struct {z {set {struct} y 2}}}))
          "unknown field")

(test/exn (interp-expr (parse '{{fun {r}
                                 {get r x}}
                            'r}))
      "free identifier")

(test/exn (interp-expr (parse '{{fun {r}
                                 {get r y}}
                            {struct {x 2} {y 'z}}}))
      "free identifier")
(test/exn (interp-expr (parse '{{fun {r}
                                 {get r y}}
                            3}))
          "expected struct")
(test/exn (interp-expr (parse '{{fun {r}
                                 {set r y 2}}
                            3}))
          "expected struct")
(test/exn (interp-expr (parse '{{fun {r}
                                 {seqn
                                  {set r x 5}
                                  {get r y}}}
                                3}))
          "expected struct")

; funky test
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
                               {fun {r} {get r a}}}
                              {fun {r} {fun {v} {set r b v}}}}
                             {struct {a 0} {b 2}}}
                            {struct {a 3} {b 4}}}))
      5)

(test/exn (interp-expr (parse '{struct {x 3} {x 2}})) "distinct")

; more tests
(test  (interp-expr (parse '(struct (x 1)))) 'struct)

; failed tests
(test (interp-expr (parse '((fun (r) (get (get r y) z)) (struct (y (struct (z 5))))))) 5)
;{with {x E1} E2} -> {{fun {x} E2} E1}
(test (interp-expr (parse '((fun (b) (get (get b x) x)) (struct (x (struct (x 111))))))) 111)
(test/exn (interp-expr (parse '((fun (s1) ((fun (s2) (get s1 a)) (struct (a 10)))) (struct)))) "unknown field")

; new
(test (interp-expr (parse '((fun (r) (get (get r y) b)) (struct (y (struct (z 5) (a 20) (b 13)) ;new
                                                                   ))))) 13)

(test (interp-expr (parse '((fun (r) (get (get r c) o)) (struct (y (struct (z 5) (a 20) (b 13))) ; new
                                                          (c (struct (m 5) (o 3) (n 13))) ; new         
                                                          )))) 3)

(test (interp-expr (parse '((fun (r) (set (get r c) o 5)) (struct (y (struct (z 5) (a 20) (b 13))) ; new
                                                                   
                                                          (c (struct (m 5) (o 4) (n 13))) ; new
                                                          )))) 4)

(test (interp-expr (parse '((fun (b) (get (get b x) x)) (struct (x (struct (x 111)) (struct (y 20) (z 13)) (struct)
                                                                   ))))) 111) ; new
