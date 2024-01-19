;;;; Scheme system

;;; globals collector

(define collect-globals
  (lambda (program kw)
    (letrec ((iter
              (lambda (program acc)
                (if (null? program)
                    acc
                    (let ((cur (car program))
                          (rest (cdr program)))
                      (cond ((and (pair? cur) (eq? (car cur) kw))
                             (iter rest
                                   (if (memq (cadr cur) acc)
                                       acc
                                       (cons (cadr cur) acc))))
                            (else
                             (iter rest acc))))))))
      (iter program '()))))

;;; macro expander

(define expand-macros
  (lambda (program)
    (letrec ((iter
              (lambda (program acc senv)
                (if (null? program)
                    (reverse acc)
                    (let* ((cur (car program))
                           (typ (if (pair? cur) (car cur) #f))
                           (rest (cdr program)))
                      (cond ((eq? typ 'define)
                                        ; variable definition
                             (let ((var (cadr cur))
                                   (definition (caddr cur)))
                               (iter rest
                                     (cons `(define ,var ,(expand definition senv))
                                           acc)
                                     senv)))
                                        ; syntax definition
                            ((eq? typ 'define-syntax)
                             (let ((kw (cadr cur))
                                   (transformer (eval (expand (caddr cur) senv)
                                                      (interaction-environment))))
                               (iter rest
                                        ; retain the statement so we can use it at runtime
                                     #;(cons cur acc)
                                     acc
                                     (cons (cons kw transformer) senv))))
                                        ; expression
                            (else
                             (iter rest
                                   (cons (expand cur senv) acc)
                                   senv)))))))
             (expand
              (lambda (e senv)
                (cond ((not (pair? e))
                       e)
                      ((eq? (car e) 'quote)
                       e)
                      ((not (symbol? (car e)))
                       (map (lambda (e) (expand e senv)) e))
                      (else
                       (let* ((h (car e))
                              (found (assq h senv)))
                         (if found
                             (expand ((cdr found) e) senv)
                             (map (lambda (e) (expand e senv)) e))))))))
      (iter program '() '()))))

;;; splice

(define splice-defs
  (lambda (program)
    (apply append
           (map (lambda (form)
                  (if (and (pair? form) (eq? (car form) 'begin))
                      (cdr form)
                      (list form)))
                program))))

(define begin->lambda-form
  (lambda (body)
    (if (null? (cdr body))
        (car body)
        (let ((first (car body))
              (rest (cdr body))
              (junk (gensym "junk")))
          `((lambda (,junk)
              ,(begin->lambda-form rest))
            ,first)))))

(define convert-sequences
  (lambda (form)
    (cond ((and (pair? form) (eq? (car form) 'begin))
           (begin->lambda-form (cdr form)))
          ((and (pair? form) (eq? (car form) 'lambda))
           `(lambda ,(cadr form)
              ,(begin->lambda-form (cddr form))))
          ((list? form)
           (map convert-sequences form))
          (else
           form))))

;;; convert-definitions

(define convert-definitions
  (lambda (program)
    (map (lambda (form)
           (cond ((and (pair? form)
                       (eq? (car form) 'define))
                  (cons 'set! (cdr form)))
                 ((and (pair? form)
                       (eq? (car form) 'define-syntax))
                  (cons 'set-syntax! (cons `(quote ,(cadr form)) (cddr form))))
                 (else
                  form)))
         program)))

;;; scheme->ast

(define scheme->ast
  (lambda (e)
    (cond ((symbol? e)
           `(var ,e))
          ((pair? e)
           (let ((h (car e)))
             (cond ((eq? h 'quote)
                    e)
                   ((eq? h 'lambda)
                    (let ((formals (cadr e))
                          (body (caddr e)))
                      `(lambda ,formals
                         ,(scheme->ast body))))
                   ((eq? h 'if)
                    (cons h (map scheme->ast (cdr e))))
                   ((eq? h '%primitive)
                    (let ((body (cdr e)))
                      (cons (car body)
                            (map scheme->ast (cdr body)))))
                   ((eq? h 'set!)
                    (let ((var (cadr e))
                          (expr (scheme->ast (caddr e))))
                      `(set! ,var ,expr)))
                   (else
                    (cons 'call (map scheme->ast e))))))
          (else
           `(quote ,e)))))

;;; check

(define safe-primitives '(var quote lambda if set! call))

(define formals?
  (lambda (formals)
    (cond ((symbol? formals)
           #t)
          ((null? formals)
           #t)
          (else
           (formals? (cdr formals))))))

(define check
  (lambda (e safe)
    (if (not (memq (car e) safe-primitives))
        (error "unsafe primitives used in safe context"))
    (let ((h (car e))
          (t (cdr e))
          (rec (lambda (e) (check e safe))))
      (cond ((memq h '(var quote))
             e)
            ((eq? h 'lambda)
             (if (not (formals? (car t)))
                 (error "invalid formals"))
             (cons h (cons (car t) (check (cadr t) safe))))
            ((eq? h 'if)
             (let ((len (length t)))
               (if (or (< len 2) (> len 3))
                   (error "invalid if"))
               (cons h (if (= len 3)
                           (map rec t)
                           (append (map rec t) '(#f))))))
            ((eq? h 'set!)
             (if (not (= (length t) 2))
                 (error "invalid set!"))
             (cons h (cons (car t) (cons (check (cadr t) safe) '()))))
            (else
             (cons h (map rec t)))))))

;;; rename

(define proper
  (lambda (l)
    (cond ((null? l)
           '())
          ((pair? l)
           (cons (car l) (proper (cdr l))))
          (else
           (list l)))))

(define map-improper
  (lambda (f l)
    (cond ((null? l)
           '())
          ((pair? l)
           (cons (f (car l)) (map-improper f (cdr l))))
          (else
           (f l)))))

(define rename-vars
  (lambda (e al)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((eq? h 'quote)
             e)
            ((eq? h 'var)
             (let* ((var (car t))
                    (found (assq var al)))
               `(var ,(if found
                          (cdr found)
                          var))))
            ((eq? h 'lambda)
             (let* ((formals (car t))
                    (body (cadr t))
                    (formal-list (proper formals))
                    (replacement (map (lambda (x) (cons x (gensym (symbol->string x))))
                                      formal-list))
                    (new-formals (map-improper (lambda (x) (cdr (assq x replacement)))
                                               formals))
                    (new-body (rename-vars body (append replacement al))))
               `(lambda ,new-formals
                  ,new-body)))
            ((eq? h 'set!)
             (let ((var (car t))
                   (expr (cadr t)))
               `(set! ,var ,(rename-vars expr al))))
            (else
             (cons h (map (lambda (e) (rename-vars e al)) t)))))))

;;; begin->lambda

(define begin->lambda
  (lambda (body)
    (if (null? (cdr body))
        (car body)
        (let ((junk (gensym "junk")))
          `(call (lambda (,junk)
                   ,(begin->lambda (cdr body)))
                 ,(car body))))))

;;; assignment conversion

(define gather-assigned
  (lambda (e acc)
    (letrec ((gather-list
              (lambda (l acc)
                (if (null? l)
                    acc
                    (gather-list (cdr l) (gather-assigned (car l) acc))))))
      (let ((h (car e))
            (t (cdr e)))
        (cond ((memq h '(var quote))
               acc)
              ((eq? h 'set!)
               (let ((found (memq (car t) acc)))
                 (gather-assigned (cadr t)
                                  (if found
                                      acc
                                      (cons (car t) acc)))))
              ((eq? h 'lambda)
               (gather-assigned (cadr t) acc))
              (else
               (gather-list t acc)))))))

(define set-add
  (lambda (s x)
    (if (memq x s)
        s
        (cons x s))))

(define set-union
  (lambda (s t)
    (if (null? t)
        s
        (set-union (set-add s (car t)) (cdr t)))))

(define convert-assignments
  (lambda (e)
    (let ((assigned (gather-assigned e '())))
      (letrec ((recurse
                (lambda (e)
                  (let ((h (car e))
                        (t (cdr e)))
                    (cond ((eq? h 'quote)
                           e)
                          ((eq? h 'set!)
                           `(ref-set! (var ,(car t)) ,(recurse (cadr t))))
                          ((eq? h 'var)
                           (if (memq (car t) assigned)
                               `(ref (var ,(car t)))
                               e))
                          ((eq? h 'lambda)
                           (let* ((assigned (filter (lambda (x)
                                                      (memq x assigned))
                                                    (proper (car t))))
                                  (new-names (map (lambda (a)
                                                    (cons a
                                                          (gensym (symbol->string a))))
                                                  assigned))
                                  (new-formals (map-improper (lambda (s)
                                                               (let ((found (memq s assigned)))
                                                                 (if found
                                                                     (cdr (assq s new-names))
                                                                     s)))
                                                             (car t))))
                             (if (null? assigned)
                                 `(lambda ,(car t) ,(recurse (cadr t)))
                                 `(lambda ,new-formals
                                    (call (lambda ,assigned
                                            ,(recurse (cadr t)))
                                          ,@(map (lambda (x)
                                                   `(make-ref (var ,(cdr x))))
                                                 new-names))))))
                          (else
                           (cons h (map recurse t))))))))
        (recurse e)))))

;;; cps

(define cps-k
  (lambda (e k)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((or (eq? h 'var) (eq? h 'quote))
             (k e))
            ((eq? h 'if)
             (let* ((ksym (gensym "k"))
                    (knew `(lambda (,ksym) ,(k `(var ,ksym)))))
               (cps-k (car t)
                      (lambda (x)
                        `(if ,x
                             ,(cps-c (cadr t) knew)
                             ,(cps-c (caddr t) knew))))))
            ((eq? h 'lambda)
             (let ((formals (car t))
                   (body (cadr t))
                   (ksym (gensym "k")))
               (k `(lambda (,ksym . ,formals)
                     ,(cps-c body `(var ,ksym))))))
            (else
             (let* ((ksym (gensym "k"))
                    (knew `(lambda (,ksym) ,(k `(var ,ksym)))))
               (cps-c e knew)))))))

(define cps-c
  (lambda (e k)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((or (eq? h 'var) (eq? h 'quote))
             `(call ,k ,e))
            ((eq? h 'if)
             (let ((ksym (gensym "k")))
               `(call (lambda (,ksym)
                        ,(cps-k (car t)
                                (lambda (x)
                                  `(if ,x
                                       ,(cps-c (cadr t) `(var ,ksym))
                                       ,(cps-c (caddr t) `(var ,ksym))))))
                      ,k)))
            ((eq? h 'lambda)
             (let ((formals (car t))
                   (body (cadr t))
                   (ksym (gensym "k")))
               `(call ,k
                      (lambda (,ksym . ,formals)
                        ,(cps-c body `(var ,ksym))))))
            ((eq? h 'call)
             (let* ((func (car t))
                    (args (cdr t)))
               (cps-k func
                      (lambda (%func)
                        (cps*-ltr args
                                  (lambda (%args)
                                    `(call ,%func ,k ,@%args)))))))
            (else
             (cps*-ltr t (lambda (%args)
                           `(call ,k (,h ,@%args)))))))))

(define cps*-ltr
  (lambda (es k)
    (if (null? es)
        (k '())
        (cps-k (car es)
               (lambda (h)
                 (cps*-ltr (cdr es)
                           (lambda (t)
                             (k (cons h t)))))))))

;;; primitive definitions

(define add-primitives
  (lambda (form)
    `(call (lambda (call/cc exit)
             ,form)
           (lambda (k f)
             (call (var f)
                   (lambda (kprime x)
                     (call (var k) (var x)))
                   (var k)))
           (lambda (x)
             (os-exit (var x))))))

;;; single-argument conversion

(define bind-arguments
  (lambda (formals argument body)
    (cond ((null? formals)
           (let ((res (gensym "res")))
             `(builtin-null? (lambda (,res)
                               (if (var ,res)
                                   ,body
                                   (error (quote "excess arguments"))))
                             (var ,argument))))
          ((symbol? formals)
           `(call (lambda (,formals)
                    ,body)
                  (var ,argument)))
          (else
           (let ((carsym (car formals))
                 (cdrsym (gensym "cdr")))
             `(builtin-car (lambda (,carsym)
                             (builtin-cdr (lambda (,cdrsym)
                                            ,(bind-arguments (cdr formals) cdrsym body))
                                          (var ,argument)))
                           (var ,argument)))))))

(define make-argument-list
  (lambda (l k)
    (if (null? l)
        `(call ,k '())
        ;`(cons ,(car l) ,(make-argument-list (cdr l)))
        (let ((ksym (gensym "k")))
          (make-argument-list (cdr l)
                              `(lambda (,ksym)
                                 (builtin-cons ,k
                                               ,(car l)
                                               (var ,ksym))))))))

(define convert-arguments
  (lambda (e)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((or (eq? h 'var) (eq? h 'quote))
             e)
            ((eq? h 'lambda)
             (let* ((formals (car t))
                    (formal-list (proper formals))
                    (body (convert-arguments (cadr t)))
                    (argument (gensym "l")))
               `(lambda (,argument)
                  ,(bind-arguments formals
                                   argument
                                   `(call (lambda ,formal-list
                                            ,body)
                                        ; put them in registers
                                          ,@(map (lambda (s)
                                                   `(var ,s))
                                                 formal-list))))))
            ((eq? h 'call)
             (let* ((l (map convert-arguments t))
                    (f (car l))
                    (args (cdr l)))
               (make-argument-list args f)))
            (else
             (cons h (map convert-arguments t)))))))

;;; closure conversion

(define make-pushlist
  (lambda ()
    (let ((l '()))
      (letrec ((push
                (lambda (x)
                  (set! l (cons x l))))
               (get
                (lambda ()
                  l))
               (dispatch
                (lambda (msg . args)
                  (cond ((eq? msg 'push)
                         (apply push args))
                        ((eq? msg 'get)
                         (apply get args))
                        (else
                         (error "pushlist: wrong message"))))))
        dispatch))))

(define substitute
  (lambda (e s)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((eq? h 'var)
             (let ((found (assq (car t) s)))
               (if found
                   (cdr found)
                   e)))
            ((eq? h 'quote)
             e)
            (else
             (cons h (map (lambda (e) (substitute e s)) t)))))))

(define make-closing-table
  (lambda (free closure)
    (letrec ((iter
              (lambda (l i)
                (if (null? l)
                    '()
                    (cons (cons (car l) `(closure-ref (var ,closure) ',i))
                          (iter (cdr l) (+ i 1)))))))
      (iter free 0))))

(define gather-free
  (lambda (e acc)
    (let ((h (car e))
          (t (cdr e)))
      (letrec ((gather-list
                (lambda (l acc)
                  (if (null? l)
                      acc
                      (gather-free (car l) (gather-list (cdr l) acc))))))
        (cond ((eq? h 'var)
               (if (memq (car t) acc)
                   acc
                   (cons (car t) acc)))
              ((eq? h 'quote)
               acc)
              (else
               (gather-list t acc)))))))

(define set-minus
  (lambda (s t)
    (if (null? t)
        s
        (if (pair? t)
            (set-minus (set-minus s (car t)) (cdr t))
            (filter (lambda (x) (not (eq? x t))) s)))))

(define convert-closures
  (lambda (e l g)
    (let ((h (car e))
          (t (cdr e)))
      (cond ((eq? h 'var)
             e)
            ((eq? h 'quote)
             e)
            ((eq? h 'lambda)
             (let* ((body (convert-closures (cadr t) l g))
                    (free (set-minus (gather-free body '())
                                     (car t)))
                    (freevarlist (map (lambda (v) `(var ,v)) free))
                    (closure-name (gensym "closure"))
                    (new-body (substitute body (make-closing-table free
                                                                   closure-name)))
                    (name (gensym "code")))
               (l 'push (cons name `(lambda ,(cons closure-name (car t))
                                      ,new-body)))
               `(make-closure (var ,name) (vector ,@freevarlist))))
            ((eq? h 'call)
             (let* ((subforms (map (lambda (e) (convert-closures e l g)) t)))
               `(call ,(car subforms) ,@(cdr subforms))))
            (else
             (cons h (map (lambda (e) (convert-closures e l g)) t)))))))

;;; maximal allocation sizes

(define max-alloc
  (lambda (body)
    (let ((h (car body))
          (t (cdr body)))
      (cond ((eq? h 'var)
             0)
            ((eq? h 'quote)
             0)
            ((eq? h 'if)
             (+ (max-alloc (car t)) (max (max-alloc (cadr t))
                                         (max-alloc (caddr t)))))
            ((eq? h 'make-ref)
             (+ 2 (max-alloc (car t))))
            ((eq? h 'vector)
             (apply + (cons (+ 1 (length t)) (map max-alloc t))))
            ((eq? h 'make-closure)
             (+ 3 (max-alloc (cadr t))))
            ((eq? h 'builtin-cons)
             (apply + (cons 3 (map max-alloc t))))
            (else
             (apply + (map max-alloc t)))))))

;;; c codegen

;; primitives:
;;   make-closure closure-ref vector
;;   builtin-car builtin-cdr builtin-null? builtin-cons
;;   make-ref ref ref-set!
;;   var if call 

(define c-charsub-table '((#\- . "_")
                  (#\space . "_space_")
                  (#\# . "_hash_")
                  (#\+ . "_plus_")
                  (#\- . "_minus_")
                  (#\* . "_ast_")
                  (#\/ . "_slash_")
                  (#\? . "_p_")
                  (#\! . "_bang_")))

(define sanitize-c-name
  (lambda (name)
    (apply string-append
           (map (lambda (c)
                  (let ((found (assoc c c-charsub-table)))
                    (if found
                        (cdr found)
                        (string c))))
                (string->list name)))))

(define string-join
  (lambda (sep sl)
    (if (null? sl)
        ""
        (apply string-append
               (cdr (apply append
                           (map (lambda (s)
                                  (list sep s))
                                sl)))))))

(define c-name
  (lambda (s)
    (if (gensym? s)
        (string-append "g_"
                       (symbol->string s)
                       "_"
                       (sanitize-c-name (gensym->unique-string s)))
        (string-append "s_"
                       (sanitize-c-name (symbol->string s))))))

(define signature
  (lambda (func)
    (let ((name (car func))
          (formals (caddr func))
          (body (cadddr func)))
      (string-append "ptr_t "
                     (c-name name)
                     "("
                     (string-join ", "
                                  (map (lambda (name)
                                         (string-append "ptr_t "
                                                        (c-name name)))
                                       formals))
                     ")"))))

(define add-const
  (lambda (e l)
    (let ((rec (lambda (e) (add-const e l))))
      (cond ((null? e)
             "make_ptr_int(2, T_SPECIAL)")
            ((boolean? e)
             (if e
                 "make_ptr_int(1, T_SPECIAL)"
                 "make_ptr_int(0, T_SPECIAL)"))
            ((pair? e)
             (string-append "cons("
                            (rec (car e))
                            ", "
                            (rec (cdr e))
                            ")"))
            ((symbol? e)
             (let* ((name (symbol->string e))
                    (len (string-length name)))
               (string-append "intern(make_ptr_ptr((ptr_t[]){"
                              "make_ptr_int("
                              (number->string len)
                              ", 3)"
                              (apply string-append
                                     (map (lambda (char)
                                            (string-append ", make_ptr_int("
                                                           (number->string
                                                            (char->integer char))
                                                           ", T_CHAR)"))
                                          (string->list name)))
                              "}, T_HEAP))")))
            ((string? e)
             (let ((len (string-length e)))
               (string-append "make_ptr_ptr((ptr_t[]){"
                              "make_ptr_int("
                              (number->string len)
                              ", 3)"
                              (apply string-append
                                     (map (lambda (char)
                                            (string-append ", make_ptr_int("
                                                           (number->string
                                                            (char->integer char))
                                                           ", T_CHAR)"))
                                          (string->list e)))
                              "}, T_HEAP)")))
            ((integer? e)
             (string-append "make_ptr_int("
                            (number->string e)
                            ", T_NUM)"))
            ((real? e)
             (string-append "make_flonum("
                            (number->string e)
                            ")"))
            ((char? e)
             (string-append "make_ptr_int("
                            (number->string (char->integer e))
                            ", T_CHAR)"))
            ((vector? e)
             (let ((len (vector-length e)))
               (string-append "((ptr_t[]){"
                              "make_ptr_int("
                              (number->string len)
                              ", 4)"
                              (apply string-append
                                     (map (lambda (e)
                                            (string-append ", "
                                                           (rec e)))
                                          (vector->list e)))
                              "})")))
            (else
             (error "object not embeddable"))))))

(define c-body
  (lambda (e cl ll)
    (let ((h (car e))
          (t (cdr e))
          (rec (lambda (e) (c-body e cl ll))))
      (cond ((eq? h 'var)
             (c-name (car t)))
            ((eq? h 'quote)
             (add-const (car t) cl))
            ((eq? h 'call)
             (let ((f-c (rec (car t)))
                   (arity (- (length t) 1))
                   (args-c (map rec (cdr t)))
                   (f-var (gensym "func")))
               (ll 'push (cons f-var f-c))
               (string-append "((ptr_t(*)("
                              (string-join ", "
                                           (make-list (+ arity 1)
                                                      "ptr_t"))
                              "))(LOAD("
                              (c-name f-var)
                              ", 1)))("
                              (c-name f-var)
                              (apply string-append
                                     (map (lambda (arg)
                                            (string-append ", "
                                                           arg))
                                          args-c))
                              ")")))
            ((eq? h 'vector) ; not general because of bad variadic functions in C
             (let ((len (length t))
                   (v-var (gensym "v")))
               (ll 'push (cons v-var (string-append "allocate("
                                                    (number->string (+ len 1))
                                                    ")")))
               (ll 'push (cons (gensym) (string-append "STORE("
                                                       (c-name v-var)
                                                       ", 0, make_ptr_int("
                                                       (number->string len)
                                                       ", 4))")))
               (letrec ((iter
                         (lambda (l i)
                           (if (null? l)
                               (if #f #f)
                               (begin
                                 (ll 'push
                                     (cons (gensym)
                                           (string-append "STORE("
                                                          (c-name v-var)
                                                          ", "
                                                          (number->string (+ i 1))
                                                          ", "
                                                          (rec (car l))
                                                          ")")))
                                 (iter (cdr l) (+ i 1)))))))
                 (iter t 0))
               (c-name v-var)))
            ((eq? h 'call)
             (let ((f (car t))
                   (args (cdr t))
                   (f-var (gensym "f")))
               (ll 'push (cons f-var (rec f)))
               (string-append "((ptr_t(*)(ptr_t"
                              (apply string-append
                                     (make-list (length args)
                                                ", ptr_t"))
                              "))"
                              (c-name f-var)
                              ")("
                              (c-name f-var)
                              (apply string-append
                                     (map (lambda (arg)
                                            (string-append ", "
                                                           (rec arg)))
                                          args))
                              ")")))
            ((eq? h 'if)
             (string-append "("
                            (rec (car t))
                            " ? "
                            (rec (cadr t))
                            " : "
                            (rec (caddr t))
                            ")"))
            (else
             (string-append (c-name h)
                            "("
                            (string-join ", "
                                         (map rec t))
                            ")"))))))

(define gen-check-gc
  (lambda (f)
    (let* ((formals (caddr f))
           (body (cadddr f))
           (max-alloc-size (max-alloc body)))
      (string-append "if (alloc + "
                     (number->string max-alloc-size)
                     " > fromspace + heap_size) { start_gc(); "
                     (apply string-append
                            (map (lambda (var)
                                   (let ((name (c-name var)))
                                     (string-append name
                                                    " = copy("
                                                    name
                                                    "); ")))
                                 formals))
                     " finish_gc(); } "))))

(define read-file
  (lambda (fn)
    (with-input-from-file fn
      (lambda ()
        (letrec ((iter
                  (lambda (acc)
                    (let ((ch (read-char)))
                      (if (eof-object? ch)
                          (apply string (reverse acc))
                          (iter (cons ch acc)))))))
          (iter '()))))))

(define write-file
  (lambda (fn content)
    (with-output-to-file fn
      (lambda ()
        (display content))
      '(replace))))

(define replace1
  (lambda (str k v)
    (let ((len (string-length str))
          (klen (string-length k)))
      (letrec ((iter
                (lambda (i)
                  (if (> (+ i klen) len)
                      str
                      (if (string=? (substring str i (+ i klen))
                                    k)
                          (string-append (substring str 0 i)
                                         v
                                         (substring str (+ i klen) len))
                          (iter (+ i 1)))))))
        (iter 0)))))

(define generate-c
  (lambda (functions entrypoint template globals)
    (let* ((constlist (make-pushlist))
           (func-decls (apply string-append
                              (map (lambda (func)
                                     (string-append (signature func)
                                                    ";\n"))
                                   functions)))
           (func-impls (apply string-append
                              (map (lambda (func)
                                     (let* ((letlist (make-pushlist))
                                            (res (c-body (cadddr func) constlist letlist)))
                                       (string-append (signature func)
                                                      " { "
                                                      (gen-check-gc func)
                                                      (apply string-append
                                                             (map (lambda (l)
                                                                    (let ((var (car l))
                                                                          (val (cdr l)))
                                                                      (string-append
                                                                       "ptr_t "
                                                                       (c-name var)
                                                                       " = "
                                                                       val
                                                                       "; ")))
                                                                  (reverse (letlist 'get))))
                                                      "return "
                                                      res
                                                      "; }\n")))
                                   functions)))
           (funcs (string-append func-decls func-impls))
           (const-decls (apply string-append
                               (map (lambda (p)
                                      (string-append "ptr_t "
                                                     (c-name p)
                                                     "; "))
                                    (append (map car (constlist 'get))
                                            globals
                                            '(call/cc)))))
           (const-assignments (apply string-append
                                    (map (lambda (p)
                                           (let ((name (car p))
                                                 (content (cdr p)))
                                             (string-append (c-name name)
                                                            " = "
                                                            content
                                                            "; ")))
                                         (reverse (constlist 'get)))))
           (globals-assignments (apply string-append
                                       (map (lambda (name)
                                              (string-append (c-name name)
                                                             " = make_ref(); "))
                                            globals))))
      
      (replace1 (replace1 template
                          "// BODY //"
                          (string-append const-assignments
                                         globals-assignments
                                         (c-name entrypoint)               
                                         "();"))                           
                "// DECLS //"                       
                (string-append const-decls funcs)))))

;;; driver

(define compile
  (lambda (program)
    (let* ((safe #f)
           (program (expand-macros program))
           (program (splice-defs program))
           (program (map convert-sequences program))
           (globals (collect-globals program 'define))
           (syntaxes (collect-globals program 'define-syntax))
           (program (convert-definitions program))
           (asts (map scheme->ast program))
           (junk (map (lambda (e) (check e safe)) asts))
           (renamed (map (lambda (e) (rename-vars e '())) asts))
           (renamed (append renamed '('0)))
           (single-form (begin->lambda renamed))
           (assignless (convert-assignments single-form))
           (cpsed (cps-c assignless '(var exit)))
           (cpsed (add-primitives cpsed))
           (known-adic (convert-arguments cpsed))
           (l (make-pushlist))
           (closed (convert-closures known-adic l globals))
           (entrypoint (gensym "main"))
           (template (read-file "program.c")))
      (l 'push (cons entrypoint `(lambda () ,closed)))
      ;(pretty-print (l 'get))
      (generate-c (l 'get) entrypoint template globals))))

(define programs
  '(((define id (lambda (x) x))
     (define list (lambda x x))
     (define first (lambda (x y z w) x y z w x))
     (first (id (list 1 (id 2) 3)) 1 2 3))
    ((define-syntax id
       (lambda (x) (cadr x)))
     (define list (lambda x x))
     (id (list (lambda (x) x) (lambda (x) x) (lambda (x) x))))))
