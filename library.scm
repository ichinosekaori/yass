;;;; rough definitions for stuff found in the standard

(define call-with-current-continuation primitive-call/cc)
(define call/cc call-with-current-continuation) ; really!

(define-syntax define-primitive
  (lambda (x)
    (let ((name (cadr x))
          (arity (caddr x)))
      (letrec ((gennsyms
                (lambda (n)
                  (if (= n 0)
                      '()
                      (cons (gensym) (gennsyms (- n 1))))))
               (gen-list-refs
                (lambda (n acc)
                  (if (= n 0)
                      acc
                      (gen-list-refs (- n 1) (cons `(list-ref x ,(- n 1)) acc))))))
       (let ((varlist (gennsyms arity)))
         `(define-syntax ,name
            (lambda (x)
              (let ,(map list varlist (gen-list-refs arity '()))
                (primitive ,name ,@varlist)))))))))

(define-primitive store! 2)
(define-primitive loadptr 1)
(define-primitive ptr-tag 1)
(define-primitive +ptr 2)
(define-primitive -ptr 2)
(define-primitive ptr-eq? 2)
(define-primitive allocate 1)

(define eq?
  (lambda (a b)
    (ptr-eq? a b)))

(define eqv? eq?)

(define equal?
  (lambda (a b)
    (cond ((or (and (boolean? a) (boolean? b))
               (and (null? a) (null? b))
               (and (symbol? a) (symbol? b))
               (and (fixnum? a) (fixnum? b))
               (and (char? a) (char? b))
               (and (port? a) (port? b))
               (and (procedure? a) (procedure? b)))
           (eq? a b))
          ((and (pair? a) (pair? b))
           (and (equal? (car a) (car b))
                (equal? (cdr a) (cdr b))))
          ((and (flonum? a) (flonum? b))
           (=. a b))
          ((and (string? a) (string? b))
           (string=? a b))
          ((and (vector? a) (vector? b))
           (if (eq? (vector-length a)
                    (vector-length b))
               (letrec ((check-equal
                         (lambda (a b s)
                           (if (= s (vector-length a))
                               #t
                               (and (equal? (vector-ref a s)
                                            (vector-ref b s))
                                    (check-equal a b (+ s 1)))))))
                 (check-equal a b 0))
               #f))
          (else
           #f))))

(define not
  (lambda (x)
    (if (eq? x #f)
        #t
        #f)))

(define cons
  (lambda (a d)
    (let ((p (allocate 3)))
      (store! p 0 0)
      (set-car! p a)
      (set-cdr! p d)
      p)))

(define list?
  (lambda (l)
    (if (null? l)
        #t
        (and (pair? l) (list? (cdr l))))))

(define list
  (lambda x x))

(define length
  (lambda (l)
    (if (null? l)
        0
        (+ (length (cdr l)) 1))))

(define reverse-append
  (lambda (l acc)
    (if (null? l)
        acc
        (iter (cdr l) (cons (car l) acc)))))

(define reverse
  (lambda (l)
    (reverse-append l '())))

(define append/2
  (lambda (a b)
    (reverse-append (reverse a) b)))

(define append
  (lambda (l)
    (cond ((null? l)
           '())
          ((null? (cdr l))
           (car l))
          (else
           (append/2 (car l) (apply append (cdr l)))))))

(define list-tail
  (lambda (l k)
    (if (= k 0)
        l
        (list-tail (cdr l) (- k 1)))))

(define list-ref
  (lambda (l k)
    (car (list-tail l k))))

(define memp
  (lambda (p)
    (letrec ((iter
              (lambda (x l)
                (if (null? l)
                    #f
                    (if (p x (car l))
                        l
                        (iter x (cdr l)))))))
      iter)))

(define memq (memp eq?))
(define memv (memp eqv?))
(define member (memp equal?))

(define assp
  (lambda (p)
    (letrec ((iter
              (lambda (x l)
                (if (null? l)
                    #f
                    (if (p x (caar l))
                        l
                        (iter (x (cdr l))))))))
      iter)))

(define assq (assp eq?))
(define assv (assp eqv?))
(define assoc (assp equal?))
