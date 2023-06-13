#lang plai

(print-only-errors)

(define-type FAE
    [num (n number?)]
    [add (lhs FAE?) (rhs FAE?)]
    [sub (lhs FAE?) (rhs FAE?)]
    [id (name symbol?)]
    [if0 (test FAE?) (then FAE?) (else FAE?)]
    [fun (param symbol?) (body FAE?)]
    [app (fun FAE?) (arg FAE?)])

(define-type FNWAE
    [W-num (n number?)]
    [W-add (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-sub (lhs FNWAE?)
           (rhs FNWAE?)]
    [W-with (name symbol?)
            (named-expr FNWAE?)
            (body FNWAE?)]
    [W-id (name symbol?)]
    [W-if0 (tst FNWAE?)
           (thn FNWAE?)
           (els FNWAE?)]
    [W-fun (params (listof symbol?))
           (body FNWAE?)]
    [W-app (fun-expr  FNWAE?)
           (arg-exprs (listof FNWAE?))])

; defsub
; this data type is either an "empty" sub or it's like a list of subs (each with a name and value)
(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value FAE-Value?) ; changed to accept an FAE
        (rest DefSub?)])

; return value of interp -- either num or closure
(define-type FAE-Value
  [numV (n number?)]
  [closureV (param-name symbol?)
            (body FAE?)
            (ds DefSub?)])


; parser produces FNWAE
; compiler translates FNWAE to FAE
; interpreter accepts FAE

; parse -> produces FNWAE
(define (parse s-exp)
  (cond
    [(number? s-exp)
     (W-num s-exp)]
    [(symbol? s-exp)
     (W-id s-exp)]
    [(and (list? s-exp) (not (empty? s-exp))) ; if our s-exp is a list, it's either add, sub, with, or app
     (case (first s-exp)
       [(+)
        (check-pieces s-exp 3 "addition")
        (W-add (parse (second s-exp))
               (parse (third s-exp)))]
       [(-)
        (check-pieces s-exp 3 "subtraction")
        (W-sub (parse (second s-exp))
               (parse (third s-exp)))]
       [(with)
        (check-pieces s-exp 3 "with")
        (check-pieces (second s-exp) 2 "with binding pair")
        (unless (symbol? (first (second s-exp)))
              (error 'parse "expected variable name, got ~a" (first (second s-exp))))
        (W-with (first (second s-exp))
                (parse (second (second s-exp)))
                (parse (third s-exp)))]
       [(if0)
        (check-pieces s-exp 4 "if0")
        (W-if0 (parse (second s-exp))
               (parse (third s-exp))
               (parse (fourth s-exp)))]
       [(fun)
        (check-pieces s-exp 3 "fun")
        
        (W-fun (second s-exp)
               (parse (third s-exp)))]
       [else
        ; make sure we have a function app (first element is an id)
        ;(unless (symbol? (first s-exp))
        ;  (error 'parse "expected application, got: ~a" s-exp))
        ; so now we know the first part is a symbol
        ; we want to create an app
        (W-app
         (parse (first s-exp)) ; the function id
         (map parse (cdr s-exp)))])] ; list of the rest of the arguments (parsed)
    [else
     (error 'parse "expected expression, got: ~a" s-exp)]))


; check-pieces helper checks length of s-exp
(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

; compiler -> FNWAE to FAE
(define (compile an-fnwae)
  (type-case FNWAE an-fnwae
    [W-num (n)
           (num n)]
    [W-add (l r)
           (add (compile l) (compile r))]
    [W-sub (l r)
           (sub (compile l) (compile r))]
    [W-with (name named-expr body)
            ; RULE: {with {x E1} E2} -> {{fun {x} E2} E1}
            (app (fun name (compile body))
                 (compile named-expr))]
    [W-id (name)
          (id name)]
    [W-if0 (test then else)
           ; possibly need to modify???
           (if0 (compile test)
                (compile then)
                (compile else))]
    [W-fun (param-name body)
           ; check for functions with no arguments
           (unless (> (length param-name) 0)
             (error "nullary function"))
           ; param-name will come in as a list -> we need to curry
           ; RULE: {fun {ID1 ID2 ID3} E} -> {fun {ID1} {fun {ID2 ID3} E}}
           (fun-compile-helper param-name body)]
    [W-app (fun-expr arg-expr)
           ; check for applications with no arguments
           (unless (> (length arg-expr) 0)
             (error "nullary application"))
           ; arg-expr will come in as a list -> we need to curry
           (app-compile-helper fun-expr arg-expr)
           ]))

(define (fun-compile-helper param body)
  (if (equal? (length param) 1)
      (fun (first param) (compile body))
      (fun (first param) (fun-compile-helper (cdr param) body))))

(define (app-compile-helper fun-name args)
  (if (equal? (length args) 1)
      (app (compile fun-name) (compile (first args)))
      (app (app-compile-helper fun-name
                               (drop-right args 1))
           ; drop right drops the last 1 element, so this returns first n-1 elements of an n length list
           (compile (last args)))))

(test/exn (compile (parse `(1))) "nullary app")
(test/exn (compile (parse `(fun () 1))) "nullary fun")

; interpreter accepts FAE (and DefSub) and outputs a FAE-Value

(define (interp an-fae ds)
  (type-case FAE an-fae
    [num (n)
         (numV n)]
    [add (l r)
         (numop + l r ds)]
    [sub (l r)
         (numop - l r ds)]
    [id (name)
        (lookup name ds)]
    [if0 (test then else)
         ; check that test is 0 AND that it's not a closure
         (define test-interped (interp test ds))
         (if (and (numV? test-interped) (equal? 0 (numV-n test-interped)))
             (interp then ds)
             (interp else ds))]

    
    [fun (param-name body)
         (closureV param-name body ds)]
    
    [app (fun-expr arg-expr)
         (define fun-val (interp fun-expr ds))

         (define arg-val (interp arg-expr ds))
        
         (type-case FAE-Value fun-val
           [closureV (param-name body closed-ds)
                     
                     (interp body
                             (aSub param-name
                                   arg-val
                                   closed-ds))]
           [else (error 'interp "expected function, got ~a" fun-val)])]))



(define (numop op l r ds)
  (define l-val (interp l ds))
  (define r-val (interp r ds))
  (unless (and (numV? l-val) (numV? r-val))
    (error 'interp "expected number"))
  (numV (op (numV-n l-val) (numV-n r-val))))

;; lookup : symbol? DefSub? -> FAE-Value?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier, got: ~a" name)]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

(define (interp-expr a-fae)
  ; IMPORTANT: interp will return FAE-Value but we want the thing itself, so we need to unpack it
  (type-case FAE-Value (interp a-fae (mtSub))
    [numV (n) n]                   ; number
    [closureV (param-name body ds)    
              'function]))         ; symbol 'function
 
(test (interp-expr (compile (parse '(if0 (if0 1 2 0) (if0 4 5 6) (if0 7 8 9))))) 6)
(test (interp-expr (compile (parse '(if0 (fun (x) x) 1 22)))) 22)
(test (interp-expr (compile (parse `(with (x (+ 5.5 9))
                                          (+ x x)))))
      29)
(test (interp-expr
  (compile (parse `(with (x 2) ((with (x 1) (fun (y) (+ x y))) x))))) 3)
(test (interp-expr (compile (parse `(with (x (+ 5 2)) (with (y (+ x x)) (+ y y)))))) 28)
(test (interp-expr (compile (parse `((fun (x y z) z) 1 0 7)))) 7)
(test (interp-expr
  (compile (parse `(with (x 100) (with (f (fun (y) (- x y))) (f 1)))))) 99)

(test (interp-expr (num 10)) 10)
(test (interp-expr (fun 'x (id 'x))) 'function)

; create PLAI-level helpers to factor out object language code
; basically, each helper takes in an s-exp as input
; then it returns the s-exp evaluated with the object-level definitions
; e.g. To call neg?, we would write ,(neg-rkt `{neg? {- a b}})
; this says to call (hence ,) neg-rkt on the s-exp `{neg? {- a b}}
; the neg-rkt function evaluates that s-exp with the object-level neg? definition in scope
; note: for mk-rec-rkt, to get recursion on a function to work, when we call it, we also need to have a helper
; function that takes in the function name as input

(define (mk-rec-rkt s-exp)
  `{with {mk-rec {fun {body-proc}
                      {with {fX {fun {fX}
                                     {with {f {fun {x}
                                                   {{fX fX} x}}}
                                           {body-proc f}}}}
                            {fX fX}}}}
                 ,s-exp})

(define (neg-rkt s-exp)
   `{with {helper ,(mk-rec-rkt `{mk-rec
                                {fun {helper}
                                     {fun {a s}
                                          {if0 a
                                               1
                                               {if0 s
                                                    0
                                                    {helper {- a 1} {+ s 1}}}}}}})}
           {with {neg? {fun {x}
                          {helper x x}}}
                 ,s-exp}})
                 
(define (mult-rkt s-exp)
  `{with {helper-pos ,(mk-rec-rkt `{mk-rec
                                    {fun {helper-pos}
                                         {fun {a b}
                                              {if0 b 0 {+ a {helper-pos a {- b 1}}}}}}})}
         {with {helper-neg ,(mk-rec-rkt `{mk-rec
                                          {fun {helper-neg}
                                               {fun {a b} {if0 b 0 {+ {- 0 a}
                                                                      {helper-neg a {+ b 1}}}}}}})}
               {with {mult {fun {x y} {if0 ,(neg-rkt `{neg? y})

                                           
                                           {helper-neg x y} {helper-pos x y}}}}
                                 ,s-exp}}})

; factorial and prime? definitions

(define factorial
  ; base case: n  = 0, return 1
  ; induct: n * factorial(n - 1)
                    
  `{fun {n1}
        {with {fac ,(mk-rec-rkt `{mk-rec
                                  {fun {fac}
                                       {fun {n}
                                            {if0 n
                                                 1
                                                 ,(mult-rkt `{mult n {fac {- n 1}}}) ; eval {...} as s-exp
                                                 }}}})}
              {fac n1}}})

(define prime?
  `{with {less-than? {fun {a b} {if0 ,(neg-rkt `{neg? {- a b}})
                                     0     ; if a is LESS than b, ret 0
                                     1}}}  ; if a >= b, ret 1
         {with {mod ,(mk-rec-rkt `{mk-rec
                                   {fun {mod}
                                        {fun {a b}
                                             {if0 {less-than? a b} ; if a < b, return a
                                                  a
                                                  {mod {- a b} b}}}}})} ; otherwise, do a - b, and check again
               ; basically, to find the remainder of x/y
               ; we can just subtract x - y - y ... until x < y
               ; whatever number remains is the remainder
               {with {helper-prime ,(mk-rec-rkt `{mk-rec
                                                  {fun {helper-prime}
                                                       {fun {na nb}
                                                            {if0 {- nb 1}
                                                                 0 ; base case: if nb == 1, we've reached the end of numbers to test, so it's prime
                                                                 {if0 {mod na nb}
                                                                      1 ; if we can divide it evenly, then it's not prime!
                                                                      {helper-prime na {- nb 1}}}}}}})} ; test with the next number
                     {fun {n}
                          {if0 n
                               1 ; if n == 0, not a prime
                               {if0 {- n 1}
                                    1 ; if n == 1, not a prime
                                    {helper-prime n {- n 1}}}}}}}})



                               
(test (interp-expr (compile (parse `(,factorial 0)))) 1)
(test (interp-expr (compile (parse `(,factorial 1)))) 1)
(test (interp-expr (compile (parse `(,factorial 2)))) 2)
(test (interp-expr (compile (parse `(,factorial 3)))) 6)
(test (interp-expr (compile (parse `(,factorial 5)))) 120)
(test (interp-expr (compile (parse `(,prime? 1)))) 1)
(test (interp-expr (compile (parse `(,prime? 0)))) 1)
(test (interp-expr (compile (parse `(,prime? 2)))) 0)
(test (interp-expr (compile (parse `(,prime? 3)))) 0)
(test (interp-expr (compile (parse `(,prime? 6)))) 1)
(test (interp-expr (compile (parse `(,prime? 7)))) 0)
(test (interp-expr (compile (parse `(,prime? 8)))) 1)
(test (interp-expr (compile (parse `(,prime? 9)))) 1)
(test (interp-expr (compile (parse `(,prime? 10)))) 1)
(test (interp-expr (compile (parse `(,prime? 14)))) 1)
(test (interp-expr (compile (parse `(,prime? 17)))) 0)
(test (interp-expr (compile (parse `(,prime? 23)))) 0)
(test (interp-expr (compile (parse `(,prime? 25)))) 1)