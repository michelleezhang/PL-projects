#lang plai

(print-only-errors)

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
       (arg-exprs (listof fnWAE?))]) ; take in a a list of fnWAEs instead of a fnWAE

(define-type FunDef
  [fundef (fun-name symbol?)
          (param-name (listof symbol?)) ; take in a list of symbols 
          (body fnWAE?)])


; check-pieces helper checks length of s-exp
(define (check-pieces exp n expected)
  (unless (= (length exp) n)
    (error 'parse "expected ~a, got: ~a" expected exp)))

; parse takes an s-exp string and converts it to a fnWAE
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


; subst
(define (subst a-fnwae name value)
  (type-case fnWAE a-fnwae
    [num (n)
         a-fnwae]
    [add (l r)
         (add (subst l name value)
              (subst r name value))]
    [sub (l r)
         (sub (subst l name value)
              (subst r name value))]
    [with (name2 named-expr body)
          (with name2 (subst named-expr name value)
                (if (equal? name name2)
                    body
                    (subst body name value)))]
    [id (name2)
        (if (equal? name name2)
            (num value)
            a-fnwae)]
    [app (fun-name arg-expr)
         ; what;s going in is (g y x)
         ; we want to replace x with 1
         ; so return app g y 1
         ; so we need to loop through argexpr

         ; so we need:
         ; first arg-expr is y
         ; look through names, no y
         ; return y
         ; next arg-expr is x
         ; look through names, x
         ; replace x = 1
         
         ; return 1
         (app fun-name
              ; arg-expr but x = 1
              (map (lambda (x) (subst x name value))
                   arg-expr))
                
         ]))

; linear search
(define (lookup-fundef name fundefs)
  (cond [(empty? fundefs)
         (error 'interp "undefined function: ~a" name)]
        [(equal? (fundef-fun-name (first fundefs)) name)
         (first fundefs)]
        [else
         (lookup-fundef name (rest fundefs))]))


; helper that basically substitutes if there's more than 1 value
; it replaces the first, then goes thru again w the newly substed thing
(define (subst-helper body names values)
  (if (equal? (length names) 0)
      body
      (subst-helper (subst body
                           (first names)
                           (first values))
                    (cdr names)
                    (cdr values))))
; helper
           
; interpreter takes in a (parsed) fnWAE and returns its result
(define (interp an-fnwae fundefs)                             
  (type-case fnWAE an-fnwae
    [num (n) n]
    
    [add (lhs rhs)
         (+ (interp lhs fundefs) (interp rhs fundefs))]
    
    [sub (lhs rhs)
         (- (interp lhs fundefs) (interp rhs fundefs))]
    
    [with (name named-expr body)
          (interp (subst body
                         name
                         (interp named-expr fundefs))
                  fundefs)]
    
    [id (name)
        (error 'interp "free identifier: ~a" name)]

    [app (fun-name arg-expr)
         (define the-fundef (lookup-fundef fun-name fundefs))

         ; check function has correct arity, error otherwise
         (unless (equal? (length (fundef-param-name the-fundef)) (length arg-expr))
           (error 'interp "wrong arity: expected ~a, got ~a" (length (fundef-param-name the-fundef)) (length arg-expr)))
         
         
         (cond
           [(equal? (length arg-expr) 0)
            (interp (fundef-body the-fundef) fundefs)]
            ; ok so we should be looking at the output of (parse '{+ {f} {f}}),
            ; which is (add (app 'f '()) (app 'f '()))

            ; from there, it goes into interp lhs
            ; from there, it goes into app
            ; so we are now looking at : app containing f ()
            ;  arg-expr here is totally empty
            ; what we want to so is repalce f with the body of the deffun
           ; so actually all we need to do is interp the body of the fundef
           
           [else
            ; so we're looking at app: f, (1 2)
            ; so fun-name = f and arg-expr = (1, 2)

            ; here the-fundef is '{deffun {f x y} {+ x y}
            ; so fundef-body = + x y
            ; and fundef-param-name = (x, y)

            ; so we need to take the fundef body, and replace the param name with the arg-exprs

            (interp
             (subst-helper (fundef-body the-fundef)
                   (fundef-param-name the-fundef)
                   (map (lambda (x) (interp x fundefs)) arg-expr))
             fundefs)

            ; we substitute in (+ x y), the values (1, 2) for (x, y)

         ])]))


(test (interp (parse '{f 1 2})
              (list (parse-defn '{deffun {f x y} {+ x y}})))
      3)

(test (interp (parse '{+ {f} {f}})
              (list (parse-defn '{deffun {f} 5})))
      10)


(test (interp (parse '(f 1 -2 3))
              (list (parse-defn '(deffun (f x y z) (- y (+ x z))))))
      -6)

;; start of reg tests

(test (interp (parse '(f 1)) (list (parse-defn '(deffun (f x) 2)))) 2)

(test (interp (parse '(f 1)) (list (parse-defn '(deffun (f x) x)))) 1)

(test (interp (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) x)))) 1)

(test (interp (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) y)))) 2)

;;;;
(test (interp (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) (g y x))) (parse-defn '(deffun (g x y) x)))) 2)

(test (interp (parse '(f 1 2)) (list (parse-defn '(deffun (f x y) (+ y x))))) 3)

(test (interp
  (parse '(f 1 2))
  (list
   (parse-defn '(deffun (f x y) (g y x)))
   (parse-defn '(deffun (g x y) y)))) 1)

(test (interp
  (parse '(f (f 1 2) (f 3 2)))
  (list
   (parse-defn '(deffun (f x y) (g y x)))
   (parse-defn '(deffun (g x y) (+ y x))))) 8)

(test (interp
  (parse '(f 1 2))
  (list (parse-defn '(deffun (f x y) (with (x 4) (+ x y)))))) 6)


(test/exn (interp (parse '{with {x y} 1})
                    (list))
            "free identifier")

  (test/exn (interp (parse '{f 1 2})
                    (list (parse-defn '{deffun {f x x} {+ x x}})))
            "bad syntax")
  (test/exn (interp (parse '{f x})
                    (list (parse-defn '{deffun {g a b c} c})))
            "undefined function")
  (test/exn (interp (parse '{f 1})
                    (list (parse-defn '{deffun {f x y} {+ x y}})))
            "wrong arity")

(test/exn (interp (parse '(f 1 2)) (list (parse-defn '(deffun (f x y z) (+ x y))))) "wrong arity")
(test/exn (interp (parse '(f 1 2 3)) (list (parse-defn '(deffun (f x y) (+ x y))))) "wrong arity")
(test/exn (parse-defn '(deffun (f x z y y z) x)) "syntax")

    