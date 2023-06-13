#lang plai

(print-only-errors)

; fnWAE
(define-type fnWAE
  [num (n number?)]
  [add (lhs fnWAE?)
       (rhs fnWAE?)]
  [sub (lhs fnWAE?)
       (rhs fnWAE?)]
  [with (name symbol?)
        (bound-expr fnWAE?)
        (body-expr fnWAE?)]
  [id (name symbol?)]
  [app (fun-name symbol?)
       (arg-expr (listof fnWAE?))] ; takes a list of fnWAEs instead of one fnWAE
  [if0 (a fnWAE?)                  ; if a == 0, then b, else c
       (b fnWAE?)
       (c fnWAE?)])

; fundef
(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?)) ; takes a list of symbols instead of one symbol
          (body fnWAE?)])

; defsub
; this data type is either an "empty" sub or it's like a list of subs (each with a name and value)
(define-type DefSub
  [mtSub]
  [aSub (name symbol?)
        (value number?)
        (rest DefSub?)])

; parse
(define (parse s-exp)
  (cond [(number? s-exp) 
         (num s-exp)]
        [(symbol? s-exp)
         (id s-exp)]
         [(and (list? s-exp) (not (empty? s-exp))) ; if our s-exp is a list, it's either add, sub, with, or app
         (case (first s-exp)
           [(+)
            (check-pieces s-exp 3 "addition")
            (add (parse (second s-exp))
                 (parse (third s-exp)))]
           [(-)
            (check-pieces s-exp 3 "subtraction")
            (sub (parse (second s-exp))
                 (parse (third s-exp)))]
           [(with)
            (check-pieces s-exp 3 "with")
            (check-pieces (second s-exp) 2 "with binding pair")
            (with (first (second s-exp))
                  (parse (second (second s-exp)))
                  (parse (third s-exp)))]
           [(if0)
            (check-pieces s-exp 4 "if0")
            (if0 (parse (second s-exp))
                 (parse (third s-exp))
                 (parse (fourth s-exp)))]
           [else
            ; make sure we have a function app (first element is an id)
            (unless (symbol? (first s-exp))
              (error 'parse "expected application, got: ~a" s-exp))
            ; so now we know the first part is a symbol
            ; we want to create an app
            (app
             (first s-exp) ; the function id
             (map parse (cdr s-exp))) ; list of the rest of the arguments (parsed)
            ])]
         
        [else
         (error 'parse "expected expression, got: ~a" s-exp)]))

; check-pieces helper checks length of s-exp
(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

; parse-defn takes in a (quoted) deffun and produces a FunDef
(define (parse-defn s-exp)
  (case (first s-exp)
    [(deffun)
     (check-pieces s-exp 3 "deffun") ; check that the deffun has 3 pieces
     ; first piece is "deffun" 
     ; second piece is the function name AND parameter NAMES
     ; third piece is the body
     (unless (equal? (length (cdr (second s-exp))) (length (remove-duplicates (cdr (second s-exp)))))
       (error 'parse-defn "bad syntax"))

     (fundef (first (second s-exp))
             (cdr (second s-exp))
             (parse (third s-exp)))]
    [else
     (error 'parse-defn "expected deffun, got: ~a" s-exp)]))

(test (parse `1) (num 1))
(test (parse `y) (id 'y))
(test (parse `{+ 1 2}) (add (num 1) (num 2)))
(test (parse `{- 1 2}) (sub (num 1) (num 2)))
(test (parse `{with {x 3} {+ x 2}}) (with 'x (num 3) (add (id 'x) (num 2))))
(test (parse `{f 10}) (app 'f (list (num 10)))) ; changed app to have list of args
(test/exn (parse `{+ 1 2 3}) "expected add")

; interp
(define (interp an-fnwae fundefs ds)
  (type-case fnWAE an-fnwae
    [num (n) n]
    [add (l r) (+ (interp l fundefs ds) (interp r fundefs ds))]
    [sub (l r) (- (interp l fundefs ds) (interp r fundefs ds))]
    [id (name)
        (lookup name ds)]
    [with (name named-expr body)
          (interp body
                  fundefs
                  (aSub name
                        (interp named-expr fundefs ds)
                        ds))]
    [if0 (a b c)
         (if (equal? (interp a fundefs ds) 0)
             (interp b fundefs ds)
             (interp c fundefs ds))]
    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))

         (define arg-values (map (lambda (x) (interp x fundefs ds)) arg-expr))
         ; here, like in hw1, need to interp each arg value in our list
         ; define above so we can check for free id error first from this interp (otherwise arity check comes first)
         
         ; check function has correct arity, error otherwise
         (unless (equal? (length (fundef-param-name the-fundef)) (length arg-expr))
           (error 'interp "wrong arity: expected ~a, got ~a" (length (fundef-param-name the-fundef)) (length arg-expr)))

         ; parse '(f 1 2) -> (app f (list (num 1) (num 2)))
         ; so now, we have alreayd loookup up the function, adn we know it is
         ; (fundef fun-name (listof param-name) body)
         ; so now we need to replace the first x in the body with 1
         ; then replace 2nd x with 2

         ; first step is substitution
         (interp (fundef-body the-fundef)
                 fundefs
                 (subst-helper (fundef-param-name the-fundef) ; name -- this is gonna be the list of arg ids
                              ; (map (lambda (x) (interp x fundefs ds)) arg-expr)
                               arg-values ; these are the values
                               (mtSub)) ; this is the rest of the subs -- iinitially, none
         )]
    ))

; helper that basically substitutes if there's more than 1 value
(define (subst-helper names values curr-defsub)
  ; need to recurse
  ; so if we have reached the end of our list
  ; return the sub
  
  (if (equal? (length names) 0)
      ; if we've run out of names, return the current DefSub
      curr-defsub
      ; otherwise, substitute recursively
      (aSub (first names)
            (first values)
            (subst-helper (cdr names)
                          (cdr values)
                          curr-defsub)))) ; call again on remaining list members


;; lookup : symbol? DefSub? -> number?
(define (lookup name ds)
  (type-case DefSub ds
    [mtSub () (error 'interp "free identifier")]
    [aSub (name2 val rest)
          (if (equal? name name2)
              val
              (lookup name rest))]))

;; lookup-fundef : symbol? (listof FunDef?) -> FunDef?
(define (lookup-fundef fun-name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" fun-name)]
        [(equal? (fundef-fun-name (first fundefs)) fun-name)
         (first fundefs)]
        [else
         (lookup-fundef fun-name (rest fundefs))]))

; interp-expr
(define (interp-expr fn-wae fundefs)
  (interp fn-wae fundefs (mtSub))) ; calls the interp so we pass in mtSub


(test (interp-expr (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) x)))) 1)
(test (interp-expr (parse '(f 11321 0)) (list (parse-defn '(deffun (f x y) y)))) 0)
(test (interp-expr (parse '(f 12 30)) (list (parse-defn '(deffun (f x y) (+ y x))))) 42)
(test (interp-expr (parse '(f)) (list (parse-defn '(deffun (f) 111)))) 111)
(test (interp-expr (parse '{+ 50 2}) '()) 52)
(test (interp-expr (parse '(f 1)) (list (parse-defn '(deffun (f x) 2)))) 2)
(test (interp-expr (parse '(f 1)) (list (parse-defn '(deffun (f x) x)))) 1)
(test (interp-expr (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) x)))) 1)
(test (interp-expr (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) y)))) 2)
(test (interp-expr (parse '(f 1 25))
                   (list (parse-defn '(deffun (f x y) (g y x))) (parse-defn '(deffun (g x y) x))))
      25)
(test (interp-expr (parse '(f 7 0))
                   (list (parse-defn '(deffun (f x y) (+ y x)))))
      7)
(test (interp-expr
  (parse '(if0 (- 1 1) (f 1) (f 1 2)))
  (list (parse-defn '(deffun (f x) (+ x 1))))) 2)
(test (interp-expr (parse '{if0 0 1 2}) '()) 1)
(test (interp-expr (parse '{if0 1 2 3}) '()) 3)
(test/exn (interp-expr
     (parse '(+ 1 (f x)))
     (list (parse-defn '(deffun (f a b c) c)))) "free identifier")
;; from the slides
(test/exn (interp-expr (parse `{with {y 2}
                                     {f 10}})
                       (list (fundef 'f (list 'x)
                                     (parse `{+ y x}))))
          "free identifier")

(test/exn (interp-expr (parse `{with {y 2}
                                     {f {+ y 8}}})
                       (list (fundef 'f (list 'x)
                                     (parse `{+ y x}))))
          "free identifier")

(test (interp-expr (parse `5) '())
      5)
(test (interp-expr (parse `{+ 1 2}) '())
      3)

(test (interp-expr (parse `{- 3 4}) '())
      -1)
(test (interp-expr (parse `{+ {+ 1 2} {- 3 4}}) '())
      2)
(test (interp-expr (parse `{with {x {+ 1 2}}
                            {+ x x}})
              '())
      6)
(test/exn (interp-expr (parse `x) '())
          "free identifier")
(test (interp-expr (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {x {- 4 3}}
                               {+ x x}}})
              '())
      8)
(test (interp-expr (parse `{+ {with {x {+ 1 2}}
                               {+ x x}}
                         {with {y {- 4 3}}
                               {+ y y}}})
              '())
      8)
(test (interp-expr (parse `{with {x {+ 1 2}}
                            {with {x {- 4 3}}
                                  {+ x x}}})
              '())
      2)
(test (interp-expr (parse `{with {x {+ 1 2}}
                            {with {y {- 4 3}}
                                  {+ x x}}})
              '())
      6)

(test/exn (interp-expr (parse `{f 10})
                       (list))
          "undefined function")

(test (interp-expr (parse `{f 10})
                   (list (fundef 'f (list 'x) (parse `{- 20 {twice {twice x}}}))
                         (fundef 'twice (list 'y) (parse `{+ y y}))))
      -20)

(test (interp-expr (parse `{f 10})
                   (list (fundef 'f (list 'x) (parse `{- 10 {twice {twice x}}}))
                         (fundef 'twice (list 'y) (parse `{+ y y}))))
      -30)



; neg and mult
; Provide a PLAI-level definition of mult-and-neg-deffuns that is bound to a list of (unparsed) def-
;funs that contains both neg? and mult as well as any helper functions you need:
(define mult-and-neg-deffuns
  (list
   `{deffun {neg? x} {helper x x}}
   `{deffun {mult x y}
      {if0 {neg? y}
           {helper-neg x y}
           {helper-pos x y}}}

      `{deffun {helper a s} {if0 a 
                              1 ; if 0, nonneg -- ret 1
                              {if0 s
                                   0
                                   {helper {- a 1}
                                           {+ s 1}}}}}
   ; if x is 0, return 1
   ; else if x is 0, return 0
   ; or check again with x - 1
   ; and check with x + 1
   ; if x - 1 is 0, return 1 (recursion means if this is ever true, x was positive)
   ; else, if x + 1 is 0, return 0 (recursion means if this is ever true, x was negative)
   ; and repeat

   ; x * y is just x + x + ... (y times) --> add up a until b is 0
      ; (increment/decrement b depending on if it's pos or neg)
   ; if b is negative
   `{deffun {helper-neg a b}
      {if0 b
           0
           {+ {- 0 a} {helper-neg a
                                  {+ b 1}}}}}

   ; if b is positive
   `{deffun {helper-pos a b}
      {if0 b
           0
           {+ a {helper-pos a
                            {- b 1}}}}}))


(test (interp-expr (parse '(neg? -1)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse '(mult -1 1)) (map parse-defn mult-and-neg-deffuns)) -1)
(test (interp-expr (parse `(neg? -100)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(neg? -15)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(neg? -0)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? -1)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(neg? 0)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? 1)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? 2)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? 3)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? 15)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(neg? 500)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(mult 0 0)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(mult 1 0)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(mult 0 1)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(mult 1 1)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(mult -1 1)) (map parse-defn mult-and-neg-deffuns)) -1)
(test (interp-expr (parse `(mult 1 -1)) (map parse-defn mult-and-neg-deffuns)) -1)
(test (interp-expr (parse `(mult -1 -1)) (map parse-defn mult-and-neg-deffuns)) 1)
(test (interp-expr (parse `(mult 1 2)) (map parse-defn mult-and-neg-deffuns)) 2)
(test (interp-expr (parse `(mult -1 2)) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse `(mult 1 -2)) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse `(mult 500 0)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(mult 0 2)) (map parse-defn mult-and-neg-deffuns)) 0)
(test (interp-expr (parse `(mult 2 530)) (map parse-defn mult-and-neg-deffuns)) 1060)
(test (interp-expr (parse `(mult -2 1)) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse `(mult 2 -1)) (map parse-defn mult-and-neg-deffuns)) -2)
(test (interp-expr (parse `(mult -20 -1)) (map parse-defn mult-and-neg-deffuns)) 20)
(test (interp-expr (parse `(mult 2.5 2)) (map parse-defn mult-and-neg-deffuns)) 5)