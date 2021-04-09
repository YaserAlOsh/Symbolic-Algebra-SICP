#lang sicp
(define pi 3.141592654)
(define (exp a b)
  (define (iter n res)
    (if (= n 0) res
        (iter
         (if (> b 0) (dec n) (inc n))
         (if (> b 0) (mul res a) (div res a)))))
  (iter b 1))
(#%require racket/base)
(define *the-table* (make-hash));make the table 
(define (put key1 key2 value) (hash-set! *the-table* (list key1 key2) value));put 
(define (get key1 key2) (hash-ref *the-table* (list key1 key2) #f));get
;For Ex 2.78, check if the obj is a number, so we don't add a tag if it is.
(define (type-tag obj) (if (number? obj) (if (eq? (round obj) obj) 'integer 'real)
                           (car obj)))
(define (contents obj) (if (number? obj) obj (cdr obj)))
(define (attach-tag tag obj) (if ;(or
                                  (eq? tag 'integer)
                                  ;(eq? tag 'integer))
                                 obj
                                 (cons tag obj)))

(define (apply-generic op . args)
  (let ((type-tags (map type-tag args)))
    (define (type-error) (error "No method for these types" (list op type-tags)))
    (let ((proc (get op type-tags)))
      (if proc
          ;Simplify is from ex 2.85
          (simplify
           (apply proc (map contents args))
           )
          
          (if (>= (length args) 2)
              ;Ex 2.84
               (let ((args-coerced (apply-raise-coercion args)))
                 (if args-coerced
                     (let ((coerced-tags (map type-tag args-coerced)))
                       (let ((types-op (get op coerced-tags)))
                         (if types-op
                              (simplify (apply types-op (map contents args-coerced)))
                              (simplify (apply-generic-successively op args-coerced))
                              )))
                     (type-error)))
               (type-error))))))
         

;(define (square x) (* x x))

(define (real-part z) (apply-generic 'real-part z))
(define (imag-part z) (apply-generic 'imag-part z))
(define (magnitude z) (apply-generic 'magnitude z))
(define (angle z)     (apply-generic 'angle z))


(define (add x y) (apply-generic 'add x y))
(define (sub x y) (apply-generic 'sub x y))
(define (mul x y) (apply-generic 'mul x y))
(define (div x y) (apply-generic 'div x y))

;Ex 2.77:
;Now calling (magnitude z) , where z is a complex number, will call apply-generic twice. First it will extract the complex tag
;then it will call the procedure magnitude on the contents, which in turn will call apply-generic with the tags '(rectangular),
;it will extract it and apply the corresponding procedure
;Ex 2.78
;Edited the tags and contents procedures above
;Ex 2.79
;Use those to handle precision errors
(define (tolerance)
 (define (try value)
   (let ((next-value (/ value 2)))
     (if (= (+ next-value 1) 1)
         value
         (try next-value))))
  (try 1.0))
(define precision (tolerance))
(define (almost-eq? x y)
  (let ((diff (magnitude (sub x y))))
    ;(or (<= sub (tolerance)) (<= (- sub) (tolerance)))))

  (or (equ? diff precision)
      (less? diff precision))))
;(define (abs-val x) (apply-generic 'abs-val x))

(define (equ? x y) (apply-generic 'equ? x y))
(define (less? x y) (apply-generic '< x y))
;Ex 2.80

(define (=zero? x) (apply-generic '=zero? x))

(define (install-real-number-package)
  (define (tag x) (attach-tag 'real x))
  ;For Ex 2.78: remove the tag call
  (put 'add '(real real)
       (lambda (x y) (tag (+ x y))))
  (put 'sub '(real real)
       (lambda (x y) (tag (- x y))))
  (put 'mul '(real real)
       (lambda (x y) (tag (* x y))))
  (put 'div '(real real)
       (lambda (x y) (tag (/ x y))))
  (put 'make 'real (lambda (x) (tag x)))

  (put 'equ? '(real real) =)
  (put '=zero? '(real) (lambda (x) (= x 0)))
  (put 'magnitude  '(real) abs)
  ;Ex 2.83
  (put 'raise '(real) (lambda (x) (make-complex-from-real-imag x 0)))
  ;Ex 2.85
  (put 'project '(real) (lambda (x) (make-integer (round x))))
  ;Ex 2.86
  (put 'square   '(real) (lambda (x) (tag (* x x))))
  (put 'sine     '(real) (lambda (x) (tag (sin x))))
  (put 'cosine   '(real) (lambda (x) (tag (cos x))))
  (put 'sqroot   '(real) (lambda (x) (tag (sqrt x))))
  (put 'tan-inv  '(real real) (lambda (x y) (tag (atan x y))))

  ;Extra
  (put '< '(real real) (lambda (x y) (< x y)))
  ;Ex 2.88
  (put 'negate '(real) (lambda (x) (tag (- x))))
  ;Ex 2.94
  (put 'gcd '(real real) (lambda (x y) (tag (gcd x y))))
  'done)

(define (make-real-number n)
((get 'make 'real) n))

(define (sign x) (if (< x 0) (- 1) 1))

(define (gcd a b)
  (if (= b 0) a
      (gcd b (remainder a b))))

(define (install-rational-package)
;; internal procedures
  (define (numer x) (car x))
  (define (denom x) (cdr x))
  (define (make-rat n d)
    (let ((reduced (reduce n d)))
      (cons (car reduced) (cadr reduced))))
    ;(let ((g (gcd n d)))
    ;  (cons (/ n g) (/ d g))))
  (define (add-rat x y)
    (make-rat (add (mul (numer x) (denom y))
                   (mul (numer y) (denom x)))
              (mul (denom x) (denom y))))
  (define (sub-rat x y)
    (make-rat (sub (mul (numer x) (denom y))
                   (mul (numer y) (denom x)))
              (mul (denom x) (denom y))))
  (define (mul-rat x y)
    (make-rat (mul (numer x) (numer y))
              (mul (denom x) (denom y))))
  (define (div-rat x y)
    (make-rat (mul (numer x) (denom y))
              (mul (denom x) (numer y))))
  ;; interface to rest of the system
  (define (tag x) (attach-tag 'rational x))
  (put 'add '(rational rational)
       (lambda (x y) (tag (add-rat x y))))
  (put 'sub '(rational rational)
       (lambda (x y) (tag (sub-rat x y))))
  (put 'mul '(rational rational)
       (lambda (x y) (tag (mul-rat x y))))
  (put 'div '(rational rational)
       (lambda (x y) (tag (div-rat x y))))
  (put 'make 'rational
       (lambda (n d) (tag (make-rat n d))))
  ;Predicates
  (put 'equ? '(rational rational) (lambda (x y) (and (= (numer x) (numer y)) (= (denom x) (denom y)))))
  ;To compare real numbers and rational, assuming that a rational number is always written in the simplest form
  (put 'equ?      '(scheme-number rational) (lambda (x y) (and (= x (numer y)) (= 1 (denom y)))))
  (put 'equ?      '(rational scheme-number) (lambda (x y) (and (= (numer x) y) (= 1 (denom x)))))
  (put '=zero?    '(rational)               (lambda (x) (=zero? (numer x) 0)))
  (put 'magnitude '(rational)               (lambda (x) (magnitude (make-real-number (exact->inexact (/ (numer x) (denom x)))))))
  ;Ex 2.83
  (put 'raise   '(rational) (lambda (x) (make-real-number (if (and (number? (numer x)) (number? (denom x)))
                                                              (/ (numer x) (denom x))
                                                              (numer x)))))
  ;Ex 2.85:
  (put 'project '(rational) (lambda (x) (make-integer (numer x))))
  ;Ex 2.86:
  (put 'square  '(rational) (lambda (x) (let ((div (/ (numer x) (denom x)))) (make-real-number (* div div)))))
  (put 'sine    '(rational) (lambda (x) (make-real-number (sin (raise-to-type (tag x) 'real)))))
  (put 'cosine  '(rational) (lambda (x) (make-real-number (cos (raise-to-type (tag x) 'real)))))
  (put 'sqroot  '(rational) (lambda (x) (make-rational (sqroot (numer x)) (sqroot (denom x)))))
  (put 'tan-inv '(rational rational) (lambda (x y) (tan-inv (raise-to-type (tag x) 'real) (raise-to-type (tag y) 'real))))

  ;Extra
  (put '<      '(rational rational) (lambda (x y) ;(let ((rat1-numer (* (numer x) (denom y)))
                                                   ;     (rat2-numer (* (numer y) (denom x)))
                                                    ;    (denom (* denom x) (denom y)))
                                                    (< (/ (numer x) (denom x)) (/ (numer y) (denom y)))))

  ;Ex 2.88
  (put 'negate '(rational) (lambda (x) (tag (make-rat (- (numer x)) (* (denom x) (sign (denom x)))))))
  ;Ex 2.94
  (put 'gcd '(rational rational) (lambda (x y) (greatest-common-divisor (div (numer x) (denom x)) (div (numer y) (denom y)))))
                                   ;(if (and (and (number? (numer x)) (number? (denom x)))
                                                ;        (and (number? (numer y)) (number? (denom y))))
                                                 ;                    (gcd (/ (numer x) (denom x)) (/ (numer y) (denom y)))
                                                  ;                   (gcd (numer x)))
                                   
  )
(define (make-rational n d)
((get 'make 'rational) n d))


(define (install-rectangular-package)
;; internal procedures
  (define (real-part z) (car z))
  (define (imag-part z) (cdr z))
  (define (make-from-real-imag x y) (cons x y))
  (define (magnitude z)
    (sqroot (add (square (real-part z))
                 (square (imag-part z)))))
  (define (angle z)
    (tan-inv (imag-part z) (real-part z)))
  (define (make-from-mag-ang r a)
    (cons (mul r (cosine a)) (mul r (sine a))))
  ;; interface to the rest of the system
  (define (tag x) (attach-tag 'rectangular x))
  (put 'real-part '(rectangular) real-part)
  (put 'imag-part '(rectangular) imag-part)
  (put 'magnitude '(rectangular) magnitude)
  (put 'angle '(rectangular) angle)
  (put 'make-from-real-imag 'rectangular
       (lambda (x y) (tag (make-from-real-imag x y))))
  (put 'make-from-mag-ang 'rectangular
       (lambda (r a) (tag (make-from-mag-ang r a))))
  ;Predicates
  (put '=zero? '(rectangular) (lambda (z) (and (=zero? (real-part z) 0) (=zero? (imag-part z) 0))))
  'done)

(define (install-polar-package)
  ;; internal procedures
  (define (magnitude z) (car z))
  (define (angle z) (cdr z))
  (define (make-from-mag-ang r a) (cons r a))
  (define (real-part z) (mul (magnitude z) (cosine (angle z))))
  (define (imag-part z) (mul (magnitude z) (sine (angle z))))
  (define (make-from-real-imag x y)
    (cons (sqroot (add (square x) (square y)))
          (tan-inv y x)))
  ;; interface to the rest of the system
  (define (tag x) (attach-tag 'polar x))
  (put 'real-part '(polar) real-part)
  (put 'imag-part '(polar) imag-part)
  (put 'magnitude '(polar) magnitude)
  (put 'angle '(polar) angle)
  (put 'make-from-real-imag 'polar
       (lambda (x y) (tag (make-from-real-imag x y))))
  (put 'make-from-mag-ang 'polar
       (lambda (r a) (tag (make-from-mag-ang r a))))

  ;Predicates
  (put '=zero? '(polar) (lambda (z) (=zero? (magnitude z) 0)))
  
  

  )



(define (install-complex-package)
;; imported procedures from rectangular and polar packages
  (define (make-from-real-imag x y)
    ((get 'make-from-real-imag 'rectangular) x y))
  (define (make-from-mag-ang r a)
    ((get 'make-from-mag-ang 'polar) r a))
  ;; internal procedures
  
  (define (add-complex z1 z2)
    (make-from-real-imag (add (real-part z1) (real-part z2))
                         (add (imag-part z1) (imag-part z2))))
  (define (sub-complex z1 z2)
    (make-from-real-imag (sub (real-part z1) (real-part z2))
                         (sub (imag-part z1) (imag-part z2))))
  (define (mul-complex z1 z2)
    (make-from-mag-ang (mul (magnitude z1) (magnitude z2))
                       (add (angle z1) (angle z2))))
  (define (div-complex z1 z2)
    (make-from-mag-ang (div (magnitude z1) (magnitude z2))
                       (sub (angle z1) (angle z2))))
  ;; interface to rest of the system
  (define (tag z) (attach-tag 'complex z))
  (put 'add '(complex complex)
       (lambda (z1 z2) (tag (add-complex z1 z2))))
  (put 'sub '(complex complex)
       (lambda (z1 z2) (tag (sub-complex z1 z2))))
  (put 'mul '(complex complex)
       (lambda (z1 z2) (tag (mul-complex z1 z2))))
  (put 'div '(complex complex)
       (lambda (z1 z2) (tag (div-complex z1 z2))))
  (put 'make-from-real-imag 'complex
       (lambda (x y) (tag (make-from-real-imag x y))))
  (put 'make-from-mag-ang 'complex
       (lambda (r a) (tag (make-from-mag-ang r a))))
  ;Ex 2.77:
  (put 'real-part '(complex) real-part)
  (put 'imag-part '(complex) imag-part)
  (put 'magnitude '(complex) magnitude)
  (put 'angle '(complex) angle)

  ;Predicates
  (put 'equ? '(complex complex) (lambda (x y) (and (almost-eq? (real-part x) (real-part y)) (almost-eq? (imag-part x) (imag-part y)))))

  (put '=zero? '(complex) =zero?)

  ;Ex 2.85:
  (put 'project '(complex) (lambda (x) (make-real-number (real-part x))))

  ;Ex 2.88
  (put 'negate '(complex) (lambda (z) (make-from-real-imag (negate (real-part z)) (negate (imag-part z)))));(make-from-mag-ang (magnitude z) (add (angle z) pi))))
  ;Ex 2.94
  (put 'gcd '(complex complex) (lambda (x y) (gcd (real-part x) (real-part y))))

  
  )

(define (make-complex-from-real-imag x y)
  ((get 'make-from-real-imag 'complex) x y))
(define (make-complex-from-mag-ang r a)
  ((get 'make-from-mag-ang 'complex) r a))


(define (install-integer-package)
  (define (tag x) (attach-tag 'integer x))
  (put 'add '(integer integer) (lambda (x y)
                                 (tag (+ (round x) (round y)))))
  (put 'sub '(integer integer) (lambda (x y)
              (tag (- (round x) (round y)))))
  (put 'mul '(integer integer) (lambda (x y)
              (tag (* (round x) (round y)))))
  (put 'div '(integer integer) (lambda (x y)
              (tag (/ x y))))
  (put 'make 'integer (lambda (x) (tag x)))
  (put 'equ? '(integer integer) (lambda (x y) (= x y)))
  (put '< '(integer integer) (lambda (x y) (< x y)))
  (put 'magnitude '(integer) abs)
  (put '=zero? '(integer) (lambda (x) (= x 0)))
  ;Ex 2.83
  (put 'raise  '(integer) (lambda (x) (make-rational (contents x) 1)))
  ;Ex 2.85
  (put 'project '(integer) (lambda (x) #f));(lambda (x) (make-integer x)))
  ;Ex 2.86
  (put 'square  '(integer) (lambda (x) (make-integer (* x x))))
  (put 'sine    '(integer) (lambda (x) (make-real-number (sin x))))
  (put 'cosine  '(integer) (lambda (x) (make-real-number (cos x))))
  (put 'sqroot  '(integer) (lambda (x) (make-real-number (sqrt x))))
  (put 'tan-inv '(integer integer) (lambda (x y) (make-real-number (atan x y))))

  ;Ex 2.88
  (put 'negate '(integer) (lambda (x) (tag (- x))))

  ;Ex 2.94
  (put 'gcd '(integer integer) (lambda (x y) (tag (gcd x y))))

  (put 'reduce '(integer integer) (lambda (n d) (tag (reduce-integers n d))))
  
  
 )

(define (make-integer n) ((get 'make 'integer) n))

(install-integer-package)


(install-real-number-package)
(install-rational-package)
(install-rectangular-package)
(install-polar-package)
(install-complex-package)





;Section 2.5.2

(define (accumulate seq proc base)
  (if (null? seq) base
      (proc (car seq) (accumulate (cdr seq) proc base))))
;Calls the nth procedure from proc-seq with the nth element from seq as argument
(define (fn-map proc-seq seq)
  (if (null? seq) '()
      (cons ((car proc-seq) (car seq)) (fn-map (cdr proc-seq) (cdr seq)))))
(define (sum seq)
  (accumulate seq + 0))
(define (all-true? seq)
  (if (null? seq) #t
      (if (car seq) (all-true? (cdr seq))
          #f)))
(define *coercion-table* (make-hash));make the table 
(define (put-coercion key1 key2 value) (hash-set! *coercion-table* (list key1 key2) value));put 
(define (get-coercion key1 key2)  (hash-ref *coercion-table* (list key1 key2) #f));get

(define (real-number->complex n)
  (make-complex-from-real-imag (contents n) 0))

(put-coercion 'real
              'complex
              real-number->complex)

(define (apply-coercion type-tags args); types-args)
  (define (try-coerce types-list)
    (if (null? types-list) #f
        (let ((types-coerced (map (lambda (t)
                                    (if (eq? t (car types-list)) (lambda (x) x) ;Use identity for args of the same type
                                        (get-coercion t (car types-list))))
                                  type-tags)))
          (if (all-true? types-coerced);If all of the types were coerced successfully
              ;Apply each coercion to each corresponding arg
              (map (lambda (p x) (p x)) types-coerced args)
              ;Otherwise
              (try-coerce (cdr types-list))   
              ))))
  (try-coerce type-tags))

(define (apply-generic-successively op args-list)
      (if (null? (cdr args-list)) (car args-list)
          (apply-generic-successively op (cons (apply-generic op (car args-list) (cadr args-list)) (cddr args-list)))))


;Ex 2.81
;a) If we call 'exp' with two complex-numbers we will run into an infinite recrusive calls,
;    because inside the apply-generic call, after we get the t1->t2 type coercion procedure,
;    we call apply-generic with the same procedure and on the same args
;b) No, the procedure will work correctly as is.
;c) We simply check if type1 and type2 are the same and stop the process if they are.

;Ex 2.82
; I have wrote apply-generic2 that can handle coercion of arbitrary types


;Ex 2.83

(define tower '(integer rational real complex polynomial))
(define (raise x) (apply-generic 'raise x))

;Ex 2.84
(define (is-higher? a1 a2 list)
  (cond ((null? list) #f)
          ((eq? (car list) a1) #f)
          ((eq? (car list) a2 ) #t)
          (else (is-higher? a1 a2 (cdr list)))))
(define (higher? type1 type2)
  (is-higher? type1 type2 tower))
  ;(define (crawl-up-tower tower)
  ;   (cond ((null? tower) #f)
  ;        ((eq? (car tower) type1) #f)
  ;        ((eq? (car tower) type2 ) #t)
  ;        (else (crawl-up-tower (cdr tower)))))
  ;(crawl-up-tower tower))

(define (raise-to-type obj target-type)
  (define (iter tower res)
    (cond ((null? (cdr tower)) res);No more types to raise to
          ((equal? (type-tag res) target-type) res);Reached the target type
          ((not (equal? (type-tag res) (car tower))) (iter (cdr tower) res));Not the type of the obj
          (else (let ((proc (get 'raise (list (car tower)))))
                  (if proc
                      (iter (cdr tower) (apply proc (list (contents res))))
                      #f)))))
  (iter tower obj))

(define (highest-type from-args)
    (define (iter args-seq res)
      (cond ((null? args-seq) res)
            ((higher? (type-tag (car args-seq)) res)
             (iter (cdr args-seq) (type-tag (car args-seq))))
            (else (iter (cdr args-seq) res))))
    (iter (cdr from-args) (type-tag (car from-args))))

(define (apply-raise-coercion args)
    (let ((target-type (highest-type args)))
     (if target-type
         (let ((raised-types (map (lambda (t) (if (eq? (type-tag t) target-type) t
                                                 (raise-to-type t target-type)))
                                 args)))
           (if (all-true? raised-types)
               raised-types
               #f))
         #f))
  )


;Ex 2.85
(define (project obj) (apply-generic 'project obj))

(define (simplify obj)
  (if (or (number? obj) (pair? obj)) (drop obj) obj))
(define (drop obj)
  (cond ;((not (pair? obj)) obj);
        ((eq? (type-tag obj) (car tower)) obj)
        (else
         (let ((project-proc (get 'project (list (type-tag obj)))))
           (if project-proc
               (let ((type (type-tag obj))
                     (projected (project-proc (contents obj))))
                 (if projected
                     (if (equ? obj (raise-to-type projected type))
                         (drop projected)
                         obj)
                     obj))
               obj)))))
         ;(let ((type (type-tag obj))
         ;      (projected (project obj)))
         ;  (if projected
          ;     (let ((raised (raise-to-type projected type)))
          ;       (if raised
           ;          (if (equ? obj raised)
           ;              (drop projected)
           ;              obj)
           ;          #f))
           ;    obj)))))

;Ex 2.86

(define (square x)  (apply-generic 'square x))
(define (sine x)    (apply-generic 'sine x))
(define (cosine x)  (apply-generic 'cosine x))
(define (sqroot x)  (apply-generic 'sqroot x))
(define (tan-inv x y) (apply-generic 'tan-inv x y))


;Section 2.5.3: Polynomial Arithmetic


;Ex 2.89 - 2.9



  

(define (install-polynomial-package)
  ;; internal procedures
  ;; representation of poly
  (define (make-poly variable term-list) (cons variable term-list))
  (define (variable p) (car p))
  (define (term-list p) (cdr p))
  (define (variable? x) (symbol? x))
  (define (same-variable? a b)
    (and (and (variable? a) (variable? b)) (eq? a b)))
  ;(define (adjoin-term term term-list)
   ; (if (=zero? (coeff term))
    ;    term-list
     ;   (cons term term-list)))
  ;; representation of terms and term lists
  
  ;(define (the-empty-termlist) '())
  ;(define (empty-termlist? term-list) (null? term-list))
  ;(define (first-term term-list) (car term-list))
  ;(define (rest-terms term-list) (cdr term-list))
  ;
  (define (make-term order coeff) (list order coeff))
  (define (order term) (car term))
  (define (coeff term) (cadr term))

  ;Polynomial operations
  (define (add-poly p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (make-poly (variable p1)
                   (add-terms (term-list p1) (term-list p2)))
        (let ((coerced (coerce-polynomials-variables p1 p2)))
          (add-poly (contents (car coerced)) (contents (cadr coerced))))))
        ;(error "Polys not in same var: ADD-POLY" (list p1 p2))))
  (define (add-terms L1 L2)
    (cond ((empty-termlist? L1) L2)
          ((empty-termlist? L2) L1)
          (else
           (let ((t1 (first-term L1))
                 (t2 (first-term L2)))
             (cond ((> (order t1) (order t2))
                    (adjoin-term
                     t1 (add-terms (rest-terms L1) L2)))
                   ((< (order t1) (order t2))
                    (adjoin-term
                     t2 (add-terms L1 (rest-terms L2))))
                   (else 
                    (adjoin-term
                     (make-term (order t1) (add (coeff t1) (coeff t2)))
                     (add-terms (rest-terms L1) (rest-terms L2)))))))))
 
  (define (mul-poly p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (make-poly (variable p1)
                   (mul-terms (term-list p1) (term-list p2)))
        (let ((coerced (coerce-polynomials-variables p1 p2)))
          (mul-poly (contents (car coerced)) (contents (cadr coerced))))))
        ;(error "Polys not in same var: MUL-POLY" (list p1 p2))))
  (define (mul-terms L1 L2)
    (if (empty-termlist? L1) L1
        (add-terms (mul-term-by-all-terms (first-term L1) L2)
                   (mul-terms (rest-terms L1) L2))))
  (define (mul-term-by-all-terms t1 L)
    (if (empty-termlist? L) L
       
        (let ((t2 (first-term L)))
          (adjoin-term
           (make-term (+ (order t1) (order t2))
                      (mul (coeff t1) (coeff t2)))
          (mul-term-by-all-terms t1 (rest-terms L))))))
  ;Ex 2.91
  (define (div-poly p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (let ((div-res (div-terms (term-list p1) (term-list p2))))
          (list
           (make-poly (variable p1) (car div-res))
           (make-poly (variable p1) (cadr div-res))))
        (error "Polys not in the same var DIV POLY" (list p1 p2))))
  (define (div-terms L1 L2)
    (if (empty-termlist? L1)
        (list L1 L1)
        (let ((t1 (first-term L1))
              (t2 (first-term L2)))
          (if (> (order t2) (order t1))
              (list (the-empty-termlist (type-tag L1)) L1)
              (let ((new-c (div (coeff t1) (coeff t2)))
                    (new-o (- (order t1) (order t2))))
                (let ((rest-of-result
                       (div-terms (add-terms L1
                                             (negate-p (mul-term-by-all-terms
                                                        (make-term new-o new-c) L2)))
                                  L2)))
                  (list (adjoin-term
                         (make-term new-o new-c)
                         (car rest-of-result))
                        (cadr rest-of-result) )))))))

  ;; interface to rest of the system
  (define (tag p) (attach-tag 'polynomial p))
  (put 'add '(polynomial polynomial)
       (lambda (p1 p2) (tag (add-poly p1 p2))))
  (put 'mul '(polynomial polynomial)
       (lambda (p1 p2) (tag (mul-poly p1 p2))))
  (put 'make 'polynomial
       (lambda (var terms) (tag (make-poly var terms))))
  (put 'div '(polynomial polynomial)
       (lambda (p1 p2) (let ((res (div-poly p1 p2))) (list (tag (car res)) (tag (cadr res))))))
  ;Ex 2.87:
  (define (zero? p-terms)
    (if (empty-termlist? p-terms) #t
        (if (=zero? (coeff (first-term p-terms)))
            (zero? (rest-terms p-terms))
            #f)))
  (put '=zero? '(polynomial) (lambda (p) (zero? (term-list p))))
  ;Ex 2.88
  (define (negate-p p)
    (if (empty-termlist? p) p
        (let ((t (first-term p)))
                  (adjoin-term (make-term (order t) (negate (coeff t)))
                               (negate-p (rest-terms p))))))
                ;(map (lambda (c) (make-term (order c) (negate (coeff c)))) (term-list p)))))
  (put 'negate '(polynomial)
       (lambda (p) (tag (make-poly (variable p) (negate-p (term-list p))))))
  (put 'sub '(polynomial polynomial)
       (lambda (p1 p2) (add (tag p1) (negate (tag p2)))))

  ;Ex 2.92
  ;(put-coercion 'integer 'polynomial (lambda (n p)
   ;                                  (make-sparse-polynomial
    ;                                  (variable p)
     ;                                 (make-term 0 n))))

  (define (coerce-polynomials-variables p1 p2)
    (let ((p1-t (first-term (term-list p1)))
              (p2-t (first-term (term-list p2))))
      (if (var-higher? (variable p1) (variable p2))
          (let ((p2-raised (if (= (order p2-t) 0) (make-sparse-polynomial (variable p1) (list p2-t))
                               (make-dense-polynomial (variable p1) (list (make-polynomial (variable p2) (term-list p2)))))))
            (list p2-raised (tag p1)))
          ;(if (= (order p2-t) 0) (make-dense-polynomial (variable p1) (list p2-t))
           ;      (list (tag p1) (make-dense-polynomial (variable p1) (list (make-polynomial (variable p2) (term-list p2))))))
          (let ((p1-raised (if (= (order p1-t) 0) (make-sparse-polynomial (variable p2) (list p1-t))
                                (make-dense-polynomial (variable p2) (list (make-polynomial (variable p1) (term-list p1)))))))
              (list p1-raised (tag p2))))))

 
  ;For Ex 2.92
  (put 'raise '(complex) (lambda (z) (make-sparse-polynomial lowest-var (list (make-term 0 (real-part z))))))

  ;Ex 2.94
  (define (remainder-terms terms-1 terms-2)
    (cadr (div-terms terms-1 terms-2)))
  
  (define (pseudoremainder-terms terms-1 terms-2)
    (let ((integerizing-factor
          (exp (coeff (first-term terms-2))
               (inc (- (order (first-term terms-1)) (order (first-term terms-2)))))))
      (if (=zero? integerizing-factor)
          (error "integerizing factor less than 0" (list terms-1 terms-2))
          (remainder-terms (mul-term-by-all-terms (make-term 0 integerizing-factor) terms-1)
                           terms-2)
          )))
  
  (define (gcd-poly p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (make-poly (variable p1)
                   (gcd-terms (term-list p1) (term-list p2)))
        (error "polys not in the same variable GCD_POLY" (list p1 p2))))
  (define (gcd-terms a b)
    (if (empty-termlist? b)
        (mul-term-by-all-terms (make-term 0 (div 1 (gcd-list a))) a)
        (gcd-terms b (pseudoremainder-terms a b))))
  
  (define (gcd-list term-list)
    (define (iter-gcd l)
      (if (null? (cdr l)) (car l)
          (gcd (car l) (iter-gcd (cdr l)))))
    (iter-gcd (coeff-list term-list)))
  
    ;(apply gcd (coeff-list term-list)))
  
    ;(let ((coeff-l (coeff-list term-list)))
     ; (iter (magnitude (car coeff-l)) (cdr coeff-l))))
    ;(iter (magnitude (coeff (first-term term-list))) term-list)) 
  (put 'gcd '(polynomial polynomial) (lambda (p1 p2) (tag (gcd-poly p1 p2))))
  ;Ex 2.97 (the last exercise! finally)

  (define (reduce-poly p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (let ((red-terms (reduce-terms (term-list p1) (term-list p2))))
          (list
           (make-poly (variable p1) (car red-terms))
           (make-poly (variable p1) (cadr red-terms))))
        (error "Polys not in the same var DIV POLY" (list p1 p2))))

  (define (reduce-terms n d)
    ;Get the gcd of the numerator and denominator
    (let ((gcd (gcd-terms n d)))
      ;Get the integerizing factor needed to make sure the result does not contain fractions. use the max of the order of n and d
      (let ((int-factor-term (make-term 0  (exp (coeff (first-term gcd))
                                                (inc (- (max (order (first-term n)) (order (first-term d))) (order (first-term gcd))))))))
        ;multiply the numerator and denominator by that int factor then divide by the gcd
        (let ((n-new (car (div-terms (mul-term-by-all-terms int-factor-term n) gcd)))
              (d-new (car (div-terms (mul-term-by-all-terms int-factor-term d) gcd))))
          ;Now reduce n-new and d-new coefficients to the lowest terms by dividing by the max of the gcd of the two term lists (n-new and d-new)
          (let ((reciprocal-max-int-factor (make-term 0 (div 1 (max (gcd-list n-new) (gcd-list d-new))))))
            (list (mul-term-by-all-terms reciprocal-max-int-factor n-new)
                  (mul-term-by-all-terms reciprocal-max-int-factor d-new)))))))
       
  ;b)
  (put 'reduce '(polynomial polynomial) (lambda (p1 p2) (let ((reduced-polys (reduce-poly p1 p2)))
                                                          (list (tag (car reduced-polys))
                                                                (tag (cadr reduced-polys))))))
  (define (poly-equ? p1 p2)
    (if (same-variable? (variable p1) (variable p2))
        (terms-equal? (term-list p1) (term-list p2))
        #f))
  (define (terms-equal? l1 l2)
    (if (and (empty-termlist? l1) (empty-termlist? l2)) #t
        (if (or (empty-termlist? l1) (empty-termlist? l2)) #f 
            (let ((t1 (first-term l1))
                  (t2 (first-term l2)))
      ;l1 (map (lambda (t) (co)
                           (if (= (order t1) (order t2))
                               (if (= (coeff  t1) (coeff t2))
                                   (terms-equal? (rest-terms l1) (rest-terms l2))
                                   #f)
                               (if (=zero? (coeff t1))
                                   (terms-equal? (rest-terms l1) l2)
                                   (if (=zero? (coeff t2))
                                       (terms-equal? l1 (rest-terms l2))
                                       #f)))))))
                                   
  (put 'equ? '(polynomial polynomial) (lambda (p1 p2) (poly-equ? p1 p2)))
  
  )
(install-polynomial-package)

(define (make-polynomial var terms)
  ((get 'make 'polynomial) var terms))



;Ex 2.88
(define (negate x) (apply-generic 'negate x))



;Ex 2.89- 2.9
(define (adjoin-term term term-list)
  ((get 'adjoin-term (type-tag term-list)) term term-list))
(define (first-term term-list)
  (apply-generic 'first-term term-list))
(define (rest-terms term-list)
  (apply-generic 'rest-terms term-list))

(define (empty-termlist? term-list)
   ((get 'empty-termlist? (type-tag term-list)) (contents term-list)))
(define (the-empty-termlist type)
  (get 'empty-termlist type))


(define (install-dense-polynomial-package)
  ;Representation
  (define (the-empty-termlist) '())
  (define (empty-termlist? term-list) (null? term-list))
  (define (first-term term-list) ;(car term-list))
    (make-term (dec (length term-list))
               (car term-list)))
  (define (rest-terms term-list) (cdr term-list))
  (define (coeff term) (cadr term))
  (define (order term) (car term)); (dec (length term-list)))
  (define (make-term order coeff) (list order coeff))

  (define (adjoin-term term term-list)
    (if (=zero? (coeff term))
       term-list
       (let ((order-t1 (order term))
             (order-t2 (dec (length term-list))))
         (if (= (- order-t1 order-t2) 1)
             (cons (coeff term) term-list)
             (adjoin-term term (cons 0 term-list))))))
           
  (define (make-from-coeff cl) (tag cl))
  (define (make-from-sparse coeff-order-pairs)
    (define (iter l)
      (cons (coeff (first-term l)) (iter (rest-terms l))))
    (iter coeff-order-pairs))
  (define (tag x) (attach-tag 'dense x))
  (put 'adjoin-term 'dense (lambda (t l) (tag (adjoin-term t (contents l)))))
  (put 'empty-termlist? 'dense empty-termlist?)
  (put 'empty-termlist 'dense (cons 'dense '()))
  (put 'first-term '(dense) first-term)
  (put 'rest-terms '(dense) (lambda (l) (tag (rest-terms l))))
  
  (put 'coeff-list 'dense (lambda (l) l))
  (put 'make-dense-termlist 'dense make-from-coeff) 
  )
(install-dense-polynomial-package)

(define (install-sparse-polynomial-package)
  ;Representation
  (define (the-empty-termlist) '())
  (define (empty-termlist? term-list) (null? term-list))
  (define (first-term term-list) (car term-list))
  (define (rest-terms term-list) (cdr term-list))
  (define (coeff term) (cadr term))
  (define (order term) (car term))
  (define (make-term order coeff) (list order coeff))
  
  (define (adjoin-term term term-list)
    (if (=zero? (coeff term))
        term-list
        (cons term term-list)))
  (define (tag x) (attach-tag 'sparse x))
  (put 'adjoin-term     'sparse (lambda (t l) (tag (adjoin-term t (contents l)))))
  (put 'empty-termlist? 'sparse empty-termlist?)
  (put 'empty-termlist  'sparse (cons 'sparse '()))
  (put 'first-term '(sparse) first-term)
  (put 'rest-terms '(sparse) (lambda (tl) (tag (rest-terms tl))))
  (put 'coeff      '(sparse) coeff)
  (put 'order      '(sparse) order)

  ;Interface
  (put 'coeff-list 'sparse (lambda (tl) (map tl coeff)))
  (put 'make-sparse-termlist 'sparse
       (lambda (termlist) (tag termlist)))
  ;(put '=zero? '(sparse) zero?)
  ;(put 'negate '(sparse) (lambda (l) (tag (negate-l l))))
  
  )
(install-sparse-polynomial-package)


(define (add-terms L1 L2)
  (apply-generic 'add-terms L1 L2))
(define (mul-terms L1 L2)
  (apply-generic 'mul-terms L1 L2))
;Ex 2.91
(define (div-terms L1 L2)
  (apply-generic 'div-terms L1 L2))

(define (make-dense-polynomial var termlist)
  (make-polynomial var ((get 'make-dense-termlist 'dense) termlist)))
(define (make-sparse-polynomial var coeff-order-pairs)
  (make-polynomial var ((get 'make-sparse-termlist 'sparse) coeff-order-pairs)))

;Ex 2.92
;suppose the order is {a , b , ... , x , y , z}
;Addition of x^2 + x + y^2 + y would leave (y^2 + y) as the constant value of the first polynomial
;Multiplication of (2x^2 + 3x)*(y+1) = (2*(y+1))x^2 + (3*(y+1))x

;First we allow operations between integers,rationals, real and complex number with polynomials by defining raise for complex numbers
;We won't do projection from polynomials to complex (real,rat etc) for now

(define var-order (list 'z 'y 'x))
(define (lowest l) (car var-order));(if (null? l) l (if (null? (cdr l)) (car l) (lowest (cdr l)))))
(define lowest-var (lowest var-order))
(define (var-higher? v1 v2) (is-higher? v1 v2 var-order))
;(define higher-var var1 var2

;Ex 2.94

(define (greatest-common-divisor a b)
  (apply-generic 'gcd a b))

;Ex 2.95
;(define p1 (make-dense-polynomial 'x (list 1 -2 1)))
;(define p2 (make-dense-polynomial 'x (list 11 0 7)))
;(define p3 (make-dense-polynomial 'x (list 13 5)))
;(define q1 (mul p1 p2))
;(define q2 (mul p1 p3))
;Ex 2.96
(define (coeff-list term-list)
  ((get 'coeff-list (type-tag term-list)) (contents term-list)))
;Ex 2.97
(define (reduce-integers n d)
    (let ((g (gcd n d)))
      (list (/ n g) (/ d g))))

(define (reduce n d)
  (apply-generic 'reduce n d))
