;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simple λ-calculus interpreter (in Scheme R5RS)
;;
;; λ-expressions are represented as follows:
;;    e ::= <symbol>             (any symbol except λ is a variable)
;;    e ::= ( λ <symbol> e )     (function abstraction)
;;    e ::= ( e e )              (function application)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define make-abs (lambda (var body) (list 'λ var body)))
(define make-app (lambda (rator rand) (list rator rand)))

(define abs? (lambda (expr) 
               (and (list? expr) (= (length expr) 3) (eqv? 'λ (car expr)))))
(define app? (lambda (expr)
               (and (list? expr) (= (length expr) 2))))
(define var? symbol?)

(define var-of cadr)
(define body-of caddr)

(define rator-of car)
(define rand-of cadr)

(define new-var
  (let ((count 0))
    (lambda ()
      (set! count (+ count 1))
      (string->symbol (string-append "new-var-" (number->string count))))))

(define exists? (lambda (p L)
                  (if (null? L) #f
                      (if (p (car L)) #t (exists? p (cdr L))))))

(define free-var? (lambda (var expr)
                    (define free-var-inner (lambda (var expr bound-vars)
                                             (cond 
                                               ((abs? expr)
                                                (free-var-inner var (body-of expr) (cons (var-of expr) bound-vars)))
                                               ((app? expr)
                                                (or
                                                 (free-var-inner var (rand-of expr) bound-vars)
                                                 (free-var-inner var (rator-of expr) bound-vars)))
                                               ((var? expr)
                                                (and (eqv? var expr) (not (exists? (lambda x (eqv? var x)) bound-vars))))
                                               (else #f))))
                    (free-var-inner var expr '())))

;; - Implements Static Binding
(define subst (lambda (e x expr)   
                (cond 
                  ((abs? expr)
                   (if (eqv? x (var-of expr))
                       expr
                       (if (free-var? (var-of expr) e)
                           (let
                               ((var (new-var)))
                             (make-abs var (subst e x (subst var (var-of expr) (body-of expr)))))
                           (make-abs (var-of expr) (subst e x (body-of expr))))))
                  ((app? expr)
                   (make-app (subst e x (rator-of expr)) (subst e x (rand-of expr))))
                  ((var? expr)
                   (if (eqv? x expr)
                       e
                       expr))
                  (else expr))))

(define (redex? expr)
  (and
   (app? expr)
   (abs? (rator-of expr))))

(define (beta redex)
  (subst
   (rand-of redex)
   (var-of (rator-of redex))
   (body-of (rator-of redex))))

(define (reduce expr)
  (define (reduce-inner expr)
    (cond
      ((var? expr) #f)
      ((abs? expr)
       (let ((body (reduce-inner (body-of expr))))
         (if body
             (make-abs (var-of expr) body)
             #f)))
      ((app? expr)
       (if (redex? expr)
           (beta expr)
           (let ((rator (reduce-inner (rator-of expr))))
             (if rator
                 (make-app rator (rand-of expr))
                 (let ((rand (reduce-inner (rand-of expr))))
                   (if rand
                       (make-app (rator-of expr) rand)
                       #f))))))))
  (let ((result (reduce-inner expr)))
    (if result
        (reduce result)
        expr)))

(define (parse-lambda expr)
  (define (prioritize e r)
    (cond
      ((null? r) e)
      ((eqv? 'λ (car r)) (list (parse-lambda e) (make-abs (parse-lambda (cadr r)) (parse-lambda (cddr r)))))
      (else (prioritize (list (parse-lambda e) (parse-lambda (car r))) (cdr r)))))
  (cond
    ((null? expr) expr)
    ((and (list? expr) (= (length expr) 1)) (parse-lambda (car expr)))
    ((and (list? expr) (eqv? (car expr) 'λ)) (make-abs (parse-lambda (cadr expr)) (parse-lambda (cddr expr))))
    ((list? expr) (prioritize (car expr) (cdr expr)))
    (else expr)))

(define (interpret E) (reduce (parse-lambda E)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define λ-true '(λ x (λ y x)))
(define λ-false '(λ x (λ y y)))
(define λ-zero '(λ f (λ x x)))
(define λ-one '(λ f (λ x (f x))))
(define λ-two '(λ f (λ x (f (f x)))))
(define λ-three '(λ f (λ x (f (f (f x))))))
(define λ-four '(λ f (λ x (f (f (f (f x)))))))
(define λ-not `(λ x (x ,λ-false ,λ-true)))
(define λ-if '(λ b (λ t (λ f ((b t) f)))))
(define λ-cons '(λ h (λ t (λ s ((s h) t)))))
(define λ-car  `(λ l (l ,λ-true)))
(define λ-cdr `(λ l (l ,λ-false)))
(define λ-nil `(λ s ,λ-true))
(define λ-null? `(λ l (l (λ h (λ t ,λ-false)))))
(define λ-zero? `(λ x (x ,λ-false ,λ-not ,λ-false)))
(define λ-succ '(λ n (λ s (λ x (s (n s x))))))
(define λ-pred `(λ n (n (λ p (λ z (z (,λ-succ (p ,λ-true)) (p ,λ-true)))) (λ z (z ,λ-zero ,λ-zero)) ,λ-false)))
(define λ-add `(λ x (λ y (x ,λ-succ y))))
(define λ-mul `(λ m (λ n (λ f (m (n f))))))
(define λ-Y '(λ f ((λ x (f (x x))) (λ x (f (x x))))))

(define λ-fib `(λ s (λ x
                      (,λ-if (,λ-zero? (,λ-pred x))
                             x
                             (,λ-add (s (,λ-pred x)) (s (,λ-pred (,λ-pred x))))))))
(define fib `(,λ-Y ,λ-fib))

(define λ-fol `(λ s (λ f (λ i (λ L (,λ-if (,λ-null? L) i (s f (f (,λ-car L) i) (,λ-cdr L))))))))
(define λ-fold `(,λ-Y ,λ-fol))
(define λ-rev `(λ x (λ y (,λ-cons x y))))
(define λ-reverse `(λ x (,λ-fold ,λ-rev ,λ-nil x)))

(define λ-fact `(λ s (λ x
                       (,λ-if (,λ-zero? x)
                              ,λ-one
                              (,λ-mul x (s (,λ-pred x)))))))
(define fact `(,λ-Y ,λ-fact))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (ok msg)
  (display "OK: ")
  (display msg)
  (newline))

(define (error msg)
  (display "ERROR: ")
  (display msg)
  (newline))

(define (assert msg b)
  (if (not b) (error msg) (ok msg)))

(define (assert-eqv msg a b)
  (assert msg (eqv? a b)))

(define (assert-equal msg a b)
  (assert msg (equal? a b)))

(define (church-to-int cn)
  (define (flatten x)
    (cond ((null? x) '())
          ((not (pair? x)) (list x))
          (else (append (flatten (car x))
                        (flatten (cdr x))))))
  (define (cn-to-int var1 l a)
    (cond
      ((null? l) a)
      ((eqv? (car l) var1) (cn-to-int var1 (cdr l) (+ a 1)))
      (else (cn-to-int var1 (cdr l) a))))
  (let ((l (flatten cn)))
    (cn-to-int (cadr l) (cddddr l) 0)))

;; substitution
(define e1 (make-abs 'x (make-abs 'y (make-app 'z 'y))))
(assert-equal "s1" e1 '(λ x (λ y (z y))))
(assert-equal "s2" (subst 'x 'z e1) '(λ new-var-1 (λ y (x y))))
(assert-equal "s3" (subst 'a 'z e1) '(λ x (λ y (a y))))
(assert-equal "s4" (subst 'y 'z e1) '(λ x (λ new-var-2 (y new-var-2))))
(assert-equal "s5" (subst '(λ y z) 'x '(λ z y)) '(λ new-var-3 y))

;; reduce
(assert-equal "r1" (reduce '((λ x x) ((λ y y) z))) 'z)
(assert-equal "r2" (reduce '(((λ z z) t) ((λ z z) y)))  '(t y))
(assert-equal "r3" (reduce '((λ x (f x))((λ y (g y)) z))) '(f (g z)))
(assert-equal "r4" (reduce '((λ x y) ((λ x (x x)) (λ x (x x))))) 'y)
(assert-equal "r5" (reduce '(λ x ((λ y (λ x (x y))) (λ z x)))) '(λ x (λ new-var-4 (new-var-4 (λ z x)))))

;; parse-lambda
(assert-equal "p1" (parse-lambda '(λ x x)) '(λ x x))
(assert-equal "p2" (parse-lambda '(λ x (x)))  '(λ x x))
(assert-equal "p3" (parse-lambda '(λ x λ y x y)) '(λ x (λ y (x y))))
(assert-equal "p4" (parse-lambda '(λ x λ z x (λ y y y) z z)) '(λ x (λ z (((x (λ y (y y))) z) z))))
(assert-equal "p5" (parse-lambda '(λ x ((x (((x))))))) '(λ x (x x)))
(assert-equal "p6" (parse-lambda '(λ x λ y y λ z x y z z)) '(λ x (λ y (y (λ z (((x y) z) z))))))

;; demonstration (fiboncci)
(assert-eqv "d1" (church-to-int (interpret `(,fib ,λ-zero))) 0)
(assert-eqv "d2" (church-to-int (interpret `(,fib ,λ-two))) 1)
(assert-eqv "d3" (church-to-int (interpret `(,fib ,λ-three))) 2)
(assert-eqv "d4" (church-to-int (interpret `(,fib ,λ-four))) 3)
;(assert-eqv "d5" (church-to-int (interpret `(,fib (,λ-mul ,λ-four ,λ-two)))) 21) ;super slow

;; demonstration (list)
(assert-eqv "d6" (church-to-int (interpret `(,λ-car (,λ-reverse (,λ-cons ,λ-one ,λ-nil))))) 1)
(assert-eqv "d7" (church-to-int (interpret `(,λ-car (,λ-reverse (,λ-cons ,λ-one (,λ-cons ,λ-two ,λ-nil)))))) 2)

;; demonstration (factorial)
(assert-eqv "d8" (church-to-int (interpret `(,fact ,λ-two))) 2)
(assert-eqv "d9" (church-to-int (interpret `(,fact ,λ-three))) 6)
