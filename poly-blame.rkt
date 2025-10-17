#lang racket
(require "utils.rkt")
(require racket/trace)

(define (print-type A)
  (match A
     ['int "\\mathtt{int}"]
     ['* "\\star "]
     [(? sym?) (sym->string A)]
     [`(-> ,A1 ,A2)
      (string-append "(" (print-type A1) "{\\to}" (print-type A2) ")")]
     [`(all ,X ,A)
      (string-append "(\\forall\\," (sym->string X) ".\\," (print-type A) ")")]
     [else (error 'print-type "unmatched ~a" A)]
     ))

(define (print-coercion p)
  (match p
     [`(id ,atm) (string-append "\\mathsf{id}_{" (print-type atm) "}")]
     [`(inj ,G) (string-append (print-type G) "!")]
     [`(proj ,G ,l) (string-append (print-type G) "?^{" (sym->string l) "}")]
     [`(-> ,c ,d)
      (string-append "(" (print-coercion c) "\\to" (print-coercion d) ")")]
     [`(all ,X ,p)
      (string-append "(\\forall\\," (sym->string X) ".\\,"(print-coercion p) ")")]
     [`(inst ,alpha ,c)
      (string-append "\\mathsf{inst}\\," (sym->string alpha) ".\\,"
                     (print-coercion c))]
     [`(gen ,alpha ,c)
      (string-append "\\mathsf{gen}\\," (sym->string alpha) ".\\,"
                     (print-coercion c))]
     [`(seal ,X)
      (string-append (sym->string X) "\\downarrow")]
     [`(unseal ,X)
      (string-append (sym->string X) "\\uparrow")]
     [`(seq ,c ,d)
      (string-append "\\left(" (print-coercion c) ";"
                     (print-coercion d) "\\right)")]
     [else (error 'print-coercion "unmatched ~a" p)]
     ))

(define (print-term e)
  (match e
     ['() "()"]
     [(? sym?)
      (sym->string e)]
     [(? integer?)
      (number->string e)]
     [`(key ,k)
      (sym->string k)]
     [`(let (,x ,e1) ,e2) 
      (string-append "\\begin{array}{l}\\mathsf{let} \\; "
		     (sym->string x)
		     " = "
		     (print-term e1)
		     "\\; \\mathsf{in} \\\\ "
		     (print-term e2)
		     "\\end{array}"
		     )]
     [`(lambda [,x : ,A] ,e1) 
      (string-append "\\left( \\lambda " (sym->string x) ":" (print-type A) ".\\, "
		     (print-term e1)
		     "\\right)")]
     [`(blame ,p)
      (string-append "\\mathsf{blame}\\," (blame->string p))]
     [`(prim ,op ,es ...)
      (string-append "(" (symbol->string op) "\\;"
		     (string-join (map print-term es) "\\;")
		     ")")]
     [`(All ,Y ,e1)
      (string-append "\\left( \\Lambda " (sym->string Y) ".\\,"
		     (print-term e1)
		     "\\right)")]
     [`(inst ,M ,A)
      (string-append (print-term M) "[" (print-type A) "]")]
     [`(cast ,e1 ,c)
      (string-append (print-term e1) "\\langle" (print-coercion c) "\\rangle")]
     [`(nu ,alpha ,B ,e1)
      (string-append "\\left(\\nu " (sym->string alpha) "{=}" 
		     (print-type B)
		     ".\\," (print-term e1)
		     "\\right)")]
     [`(,e1 ,e2)
      (string-append (print-term e1) "\\cdot " (print-term e2))]
     [else
      (error 'print-term "unmatched ~s" e)]
     ))

(define (type-subst B X A)
  (match B
     [`int 'int]
     [`bool 'bool]
     [`* '*]
     [(? sym?)
      (cond [(equal? B X) A]
	    [else B])]
     [`(-> ,C ,D)
      `(-> ,(type-subst C X A) ,(type-subst D X A))]
     [`(all ,Y ,C)
      (cond [(equal? X Y) `(all ,Y ,C)]
	    [else ;; to do: free-variable capture
	     `(all ,Y ,(type-subst C X A))])]
     ))

(define (ground? A)
  (match A
     [`int #t]
     [`bool #t]
     [`(-> * *) #t]
     [(? sym?) #t]
     [else #f]))

(define (less-precise? dyn-vars A B tv-rel)
  (define result
  (match* (A B)
     [('int 'int) #t]
     [('bool 'bool) #t]
     [('* '*) #t]
     [('* (? ground?)) #t]
     [('* (? sym?))
      (set-member? dyn-vars B)]
     [((? sym?) (? sym?)) #:when (eq? A B)
      #t]
     [((? sym?) (? sym?)) #:when (dict-has-key? tv-rel A)
      (eq? (dict-ref tv-rel A) B)]
     [((? sym?) (? sym?))
      (dict-set! tv-rel A B)
      #t]
     [('* `(-> ,C ,D))
      (and (less-precise? dyn-vars '* C tv-rel)
           (less-precise? dyn-vars '* D tv-rel))]
     [(`(-> ,A ,B) `(-> ,C ,D))
      (and (less-precise? dyn-vars A C tv-rel)
           (less-precise? dyn-vars B D tv-rel))]
     [(`(all ,X ,A) `(all ,Y ,B))
      (dict-set! tv-rel X Y)
      (less-precise? dyn-vars A B tv-rel)]
     [(A `(all ,Y ,B))
      (less-precise? (set-add dyn-vars Y) A B tv-rel)]
     [(A B) #f]))
  result)

(define (consistent? dyn-vars A B)
  (define result
  (match* (A B)
     [('int 'int) #t]
     [('bool 'bool) #t]
     [('* '*) #t]
     [('* (? ground?)) #t]
     [((? ground?) '*) #t]
     [((? sym?) '*)
      (set-member? dyn-vars A)]
     [('* (? sym?))
      (set-member? dyn-vars B)]
     [((? sym?) (? sym?))
      (eq? A B)]
     [('* `(-> ,C ,D))
      (and (consistent? dyn-vars '* C)
           (consistent? dyn-vars '* D))]
     [(`(-> ,A ,B) '*)
      (and (consistent? dyn-vars A '*)
           (consistent? dyn-vars B '*))]
     [(`(-> ,A ,B) `(-> ,C ,D))
      (and (consistent? dyn-vars A C)
           (consistent? dyn-vars B D))]
     [(`(all ,X ,A) `(all ,Y ,B))
      (consistent? dyn-vars A (type-subst B Y X))]
     [(`(all ,X ,A) B)
      (consistent? (set-add dyn-vars X) A B)]
     [(A `(all ,Y ,B))
      (consistent? (set-add dyn-vars Y) A B)]
     [(A B) #f]))
  result)

(define (make-coercion A B label inst-vars gen-vars)
  (define result
  (match* (A B)
     [('int 'int) `(id int)]
     [('bool 'bool) `(id bool)]
     [('* '*) `(id *)]
     [((? sym?) (? sym?)) #:when (eq? A B)
      `(id ,A)]
     [((? sym?) B) #:when (set-member? inst-vars A)
      `(unseal ,A)]
     [(A (? sym?)) #:when (set-member? inst-vars B)
      `(seal ,B)]
     [((? sym?) '*) #:when (set-member? gen-vars A)
      `(inj ,A)]
     [('* (? sym?)) #:when (set-member? gen-vars B)
      `(proj ,B ,label)]
     [((? ground?) '*)
      `(inj ,A)]
     [('* (? ground?))
      `(proj ,B ,label)]
     [(`(-> ,A ,B) `(-> ,C ,D))
      `(-> ,(make-coercion C A label inst-vars gen-vars)
           ,(make-coercion B D label inst-vars gen-vars))]
     [('* `(-> ,C ,D))
      `(-> ,(make-coercion C '* label inst-vars gen-vars)
           ,(make-coercion '* D label inst-vars gen-vars))]
     [(`(-> ,A ,B) '*)
      `(-> ,(make-coercion '* A label inst-vars gen-vars)
           ,(make-coercion B '* label inst-vars gen-vars))]
     [(`(all ,X ,A) `(all ,Y, B))
      `(all ,X ,(make-coercion A (type-subst B Y X) label inst-vars gen-vars))]
     [(`(all ,X ,A) B)
      `(inst ,X ,(make-coercion A B label (set-add inst-vars X) gen-vars))]
     [(A `(all ,X ,B))
      `(gen ,X ,(make-coercion A B label inst-vars (set-add gen-vars X)))]
     [(A B)
      (error 'make-coercion "error ~a ~a\nin: ~a\nand: ~a" A B (set->list inst-vars)
             (set->list gen-vars))]))
  result)

(define (type-app L A X B label)
  (define alpha (gensym X))
  `(nu ,alpha ,A (cast (inst ,L ,alpha) ,(make-coercion (type-subst B X alpha)
                                                        (type-subst B X A)
                                                        label
                                                        (set alpha)
                                                        (set)))))

(define (cast-insert-term e type-env)
  (match e
     [(? sym?)
      (values e (lookup e type-env))]
     [(? integer?)
      (values e 'int)]
     [(? boolean?)
      (values e 'bool)]
     [`(let (,x ,e1) ,e2) 
      (define-values (e1^ t1) (cast-insert-term e1 type-env))
      (define-values (e2^ t2) (cast-insert-term e2 (extend type-env x t1)))
      (values `(let (,x ,e1^) ,e2^) t2)]
     [`(lambda [,x : ,A] ,e1) 
      (define-values (e1^ B) (cast-insert-term e1 (extend type-env x A)))
      (values
       `(lambda [,x : ,A] ,e1^)
       `(-> ,A ,B))]
     [`(All ,Y ,e1)
      (define-values (e1^ A) (cast-insert-term e1 type-env))
      (values
       `(All ,Y ,e1^)
       `(all ,Y ,A))]
     [`(prim ,op ,es ...)
      (define-values (new-es ts)
        (for/lists (l1 l2) ([e es]) (cast-insert-term e type-env)))
      (type-check-op op ts)
      (values
       `(prim ,op ,new-es ...)
       (return-type op))]
     [`(inst ,e1 ,A ,label)
      (define-values (e1^ B1) (cast-insert-term e1 type-env))
      (match B1
         [`(all ,X ,B)
          (values
           (type-app e1^ A X B label)
           (type-subst B X A))]
         [else
          (error 'cast-insert-term "inst expected an all, not ~a" B1)])]
     [`(,e1 ,e2 ,label)
      (define-values (e1^ F) (cast-insert-term e1 type-env))
      (define-values (e2^ A) (cast-insert-term e2 type-env))
      (match F
         [`(-> ,Ap ,Bp)
          (if (not (consistent? (set) A Ap))
              (error 'cast-insert-term "in call, param type ~a but arg type ~a" Ap A)
              (void))
          (values
           `(,e1^ (cast ,e2^ ,(make-coercion A Ap label (set) (set))))
           Bp)]
         [`*
          (values
           `(,e1^ (cast ,e2^ ,(make-coercion A '* label (set) (set))))
           '*)]
         [else
          (error 'cast-insert-term "expected a function, not ~a" F)])]
     [else
      (error 'cast-insert-term "unmatched ~s" e)]
     ))

(define (type-equal? t1 t2)
  (match (cons t1 t2)
         [`(int . int) #t]
         [`(bool . bool) #t]
         [`(* . *) #t]
         [`(,X . ,Y) #:when (and (sym? X) (sym? Y) (eq? X Y)) #t]
         [`((-> ,A ,B) . (-> ,C ,D))
          (and (type-equal? A C)
               (type-equal? B D))]
         [`((all ,X ,A) . (all ,Y ,B))
          (type-equal? A (type-subst B Y X))]
         [else
          #f]))

(define (type-check-coercion p type-env)
  (define-values (src tgt)
  (match p
     [`(id ,A)
      (values A A)]
     [`(inj ,G) #:when (ground? G)
      (values G '*)]
     [`(proj ,G ,l) #:when (ground? G)
      (values '* G)]
     [`(seal ,X)
      (define A (lookup X type-env))
      (values A X)]
     [`(unseal ,X)
      (define A (lookup X type-env))
      (values X A)]
     [`(-> ,c ,d)
      (define-values (C A) (type-check-coercion c type-env))
      (define-values (B D) (type-check-coercion d type-env))
      (values `(-> ,A ,B) `(-> ,C ,D))]
     [`(all ,X ,c)
      (define-values (A B) (type-check-coercion c type-env))
      (values `(all ,X ,A) `(all ,X ,B))]
     [`(gen ,X ,c)
      (define new-env (extend type-env X '*))
      (define-values (A B) (type-check-coercion c new-env))
      (values A `(all ,X ,B))]
     [`(inst ,X ,c)
      (define new-env (extend type-env X '*))
      (define-values (A B) (type-check-coercion c new-env))
      (values `(all ,X ,A) B)]
     [`(seq ,c ,d)
      (define-values (A B) (type-check-coercion c type-env))
      (define-values (B^ C) (type-check-coercion d type-env))
      (if (not (type-equal? B B^))
          (error 'type-check-coercion "seq: ~a != ~a" B B^)
          (void))
      (values A C)]
     [else (error 'type-check-coercion "unmatched ~a" p)]
     ))
  (values src tgt))

(define (type-check-op op Ts)
  (andmap (map (lambda (T) (equal? T 'int)))))

(define (return-type op)
  'int)

(define (type-check e type-env)
  (match e
     [(? sym?)
      (lookup e type-env)]
     [(? integer?)
      'int]
     [(? boolean?)
      'bool]
     [`(let (,x ,e1) ,e2) 
      (define A (type-check e1 type-env))
      (define B (type-check e2 (extend type-env x A)))
      B]
     [`(lambda [,x : ,A] ,e1) 
      (define B (type-check e1 (extend type-env x A)))
      `(-> ,A ,B)]
     [`(All ,Y ,e1)
      (define A (type-check e1 type-env))
      `(all ,Y ,A)]
     [`(prim ,op ,es ...)
      (define  ts (for/list ([e es]) (type-check e type-env)))
      (type-check-op op ts)
      (return-type op)]
     [`(inst ,e1 ,A)
      (define B1 (type-check e1 type-env))
      (match B1
         [`(all ,X ,B)
          (type-subst B X A)]
         [else
          (error 'type-check "inst expected an all, not ~a" B1)])]
     [`(nu ,X ,A ,e1)
      (define B (type-check e1 (extend type-env X A)))
      ;; TODO: check that X not in FV(B)
      B]
     [`(cast ,e1 ,c)
      (define A (type-check e1 type-env))
      (define-values (A^ B) (type-check-coercion c type-env))
      (if (not (type-equal? A A^))
          (error 'type-check "cast: source type ~a not equal body type ~a" A^ A)
          (void))
      B]
     [`(,e1 ,e2)
      (define F (type-check e1 type-env))
      (define A (type-check e2 type-env))
      (match F
         [`(-> ,Ap ,Bp)
          (if (not (type-equal? A Ap))
              (error 'type-check "~a != ~a" A Ap)
              (void))
          Bp]
         [else
          (error 'type-check "expected a function, not ~a" F)])]
     [else
      (error 'type-check "unmatched ~s" e)]
     ))


(define (subst e y v)
  (match e
     [(? sym?)
      (cond [(equal? e y) v]
	    [else e])]
     [(? integer?)
      e]
     [(? boolean?)
      e]
     [`(let (,x ,e1) ,e2) 
      `(let (,x ,(subst e1 y v))
	 ,(cond [(equal? x y) e2]
		[else (subst e2 y v)]))]
     [`(lambda [,x : ,T] ,e1) 
      (cond [(equal? x y)
	     `(lambda [,x : ,T] ,e1)]
	    [else
	     `(lambda [,x : ,T] ,(subst e1 y v))])]
     [`(All ,X ,e1)
      `(All ,X ,(subst e1 y v))]
     [`(cast ,e1 ,c)
      `(cast ,(subst e1 y v) ,c)]
     [`(nu ,alpha ,A ,e1)
      `(nu ,alpha ,A ,(subst e1 y v))]
     [`(blame ,p)
      `(blame ,p)]
     [`(prim ,op ,es ...)
      `(prim ,op ,@(map (lambda (e) (subst e y v)) es))]
     [`(inst ,e1 ,A)
      `(inst ,(subst e1 y v) ,A)]
     [`(,e1 ,e2)
      `(,(subst e1 y v) ,(subst e2 y v))]
     [else
      (error 'subst "unmatched ~s" e)]
     ))

(define (type-term-subst e X A)
  (match e
     [(? sym?)
      e]
     [(? integer?)
      e]
     [(? boolean?)
      e]
     [`(let (,x ,e1) ,e2) 
      `(let (,x ,(type-term-subst e1 X A)) 
	 ,(type-term-subst e2 X A))]
     [`(lambda [,x : ,B] ,e1) 
      `(lambda [,x : ,(type-subst B X A)]
	 ,(type-term-subst e1 X A))]
     [`(All ,Y ,e1)
      (define Y^ (gensym Y))
      `(All ,Y^ ,(type-term-subst (type-term-subst e1 Y Y^) X A))]
     [`(cast ,e1 ,p)
      `(cast ,(type-term-subst e1 X A) ,(coercion-subst p X A))]
     [`(nu ,alpha ,B ,e1)
      (define alpha^ (gensym alpha))
      `(nu ,alpha^ ,B ,(type-term-subst (type-term-subst e1 alpha alpha^) X A))]
     [`(blame ,p)
      `(blame ,p)]
     [`(prim ,op ,es ...)
      `(prim ,op ,@(map (lambda (e) (type-term-subst e X A)) es))]
     [`(inst ,e1 ,B)
      `(inst ,(type-term-subst e1 X A) ,(type-subst B X A))]
     [`(,e1 ,e2)
      `(,(type-term-subst e1 X A) ,(type-term-subst e2 X A))]
     [else
      (error 'type-term-subst "unmatched ~s" e)]
     ))

(define (blame? e)
  (match e
    [`(blame ,l)  #t]
    [else #f]))

(define (value? e)
  (match e
     [(? integer?)  #t]
     [(? boolean?)  #t]
     [`(lambda [,x : ,T] ,e)  #t]
     [`(All ,X ,v) (value? v)]
     [`(cast ,v (inj ,G)) (value? v)]
     [`(cast ,v (seal ,X)) (value? v)]
     [`(cast ,v (-> ,c ,d))  (value? v)]
     [`(cast ,v (gen ,X ,c))  (value? v)]
     [`(cast ,v (all ,X ,c))  (value? v)]
     [else #f]
     ))

(define (reduce e type-env)
  (match e
     ;; new type generation
     [`(nu ,alpha ,A ,e1)
      (define alpha^ (gensym alpha))
      (values (type-term-subst e1 alpha alpha^)
            (extend type-env alpha^ A))]
     [else
      (values (pure-reduce e) type-env)]))
  
(define (add x y) (+ x y))
(define (sub x y) (- x y))
(define (mul x y) (* x y))
(define (div x y) (/ x y))

(define operators
  `((+ . ,add)
    (- . ,sub)
    (* . ,mul)
    (/ . ,div)
    ))

(define (coercion-subst p X alpha)
  (match p
     [`(id ,A) `(id ,(type-subst A X alpha))]
     [`(inj ,G) `(inj ,(type-subst G X alpha))]
     [`(proj ,G ,l) `(proj ,(type-subst G X alpha) ,l)]
     [`(-> ,p ,q)
      `(-> ,(coercion-subst p X alpha) ,(coercion-subst q X alpha))]
     [`(all ,Y ,p)
      (define Y^ (gensym Y))
      `(all ,Y^ ,(coercion-subst (coercion-subst p Y Y^) X alpha))]
     [`(inst ,beta ,p)
      (define beta^ (gensym beta))
      `(inst ,beta^
             ,(coercion-subst (coercion-subst p beta beta^) X alpha))]
     [`(gen ,beta ,p)
      (define beta^ (gensym beta))
      `(gen ,beta^
             ,(coercion-subst (coercion-subst p beta beta^) X alpha))]
     [`(seal ,beta)
      `(seal ,(type-subst beta X alpha))]
     [`(unseal ,beta)
      `(unseal ,(type-subst beta X alpha))]
     [`(seq ,p1 ,p2)
      `(seq ,(coercion-subst p1 X alpha) ,(coercion-subst p2 X alpha))]
     [else (error 'coercion-subst "unmatched ~a" p)]
     ))

(define (pure-reduce e)
  (match e
     ;; System F Reduction Rules
     [`(prim ,op ,vs ...) #:when (andmap value? vs)
      (apply (cdr (assq op operators)) vs)]
     [`(let (,x ,v) ,e1) #:when (value? v)
      (subst e1 x v)]
     [`((lambda [,x : ,T] ,e) ,w) #:when (value? w)
      (subst e x w)]
     [`(inst (All ,X ,e1) ,alpha)
      (type-term-subst e1 X alpha)]

     ;; Cast Reduction Rules
     
     [`(cast ,v (seq ,c ,d))  #:when (value? v)
      `(cast (cast ,v ,c) ,d)]
     
     ;; identity
     [`(cast ,v (id ,atm)) #:when (value? v)
      v]
     
     ;; wrap function
     [`((cast ,v (-> ,c ,d)) ,w) #:when (and (value? v) (value? w))
      `(cast (,v (cast ,w ,c)) ,d)]

     ;; all coercion and type application
     [`(inst (cast ,v (all ,X ,c)) ,beta)
      `(cast (inst ,v ,beta)
             ,(coercion-subst c X beta))]
     
     ;; generalize and type application
     [`(inst (cast ,v (gen ,alpha ,c)) ,beta)
      `(cast ,v ,(coercion-subst c alpha beta))]
     
     ;; instantiate coercion
     [`(cast ,v (inst ,X ,c))
      (define X^ (gensym X))
      `(nu ,X^ * (cast (inst ,v ,X^) ,(coercion-subst c X X^)))]
     
     ;; inj/proj
     [`(cast (cast ,v (inj ,G)) (proj ,H ,label))
      #:when (equal? G H)
      v]
     ;; conflict
     [`(cast (cast ,v (inj ,G)) (proj ,H ,label))
      #:when (not (equal? G H))
      `(blame ,label)]
     ;; seal/unseal
     [`(cast (cast ,v (seal ,alpha)) (unseal ,beta))
      #:when (equal? alpha beta)
      v]

     [else
      (error 'reduce "not reducible ~a" e)
      `777]
     ))

(define plug
  (lambda (ctx e)
    (match ctx
      [`() e]
      [`((let (,x [-]) ,e1) . ,ctx)
       (plug ctx `(let (,x ,e) ,e1))]
      [`((prim ,op ,vs ... [-] ,es ...) . ,ctx)
       (plug ctx `(prim ,op ,@vs ,e ,@es))]
      [`((cast [-] ,p) . ,ctx)
       (plug ctx `(cast ,e ,p))]
      [`((nu ,alpha ,A [-]) . ,ctx)
       (plug ctx `(nu ,alpha ,A ,e))]
      [`((inst [-] ,A) . ,ctx)
       (plug ctx `(inst ,e ,A))]
      [`((,e1 [-]) . ,ctx)
       (plug ctx `(,e1 ,e))]
      [`(([-] ,e2) . ,ctx)
       (plug ctx `(,e ,e2))]
      [else
       (error 'plug "unmatched ~a" ctx)]
      )))

(define (decompose e ctx)
  (match e
    [(? value?)
     (cons ctx e)]
    [`(cast ,e ,p)
     (cond [(value? e)
	    (cons ctx `(cast ,e ,p))]
	   [else
	    (decompose e (cons `(cast [-] ,p) ctx))])]
    [`(let (,x ,e1) ,e2)
     (cond [(value? e1)
	    (cons ctx `(let (,x ,e1) ,e2))]
	   [else
	    (decompose e1 (cons `(let (,x [-]) ,e2) ctx))])]
    [`(prim ,op ,es ...)
     (let loop ([es es] [vs '()])
       (cond [(null? es)
	      (cons ctx `(prim ,op ,@vs))]
	     [(value? (car es))
	      (loop (cdr es) (cons (car es) vs))]
	     [else
	      (decompose (car es) (cons `(prim ,op ,@vs [-] ,@(cdr es)) ctx))]
	     ))]
    [`(nu ,alpha ,A ,e)
     (cons ctx `(nu ,alpha ,A ,e))]
    [`(inst ,e1 ,A)
     (cond [(value? e1)
	    (cons ctx `(inst ,e1 ,A))]
	   [else
	    (decompose e1 (cons `(inst [-] ,A) ctx))])]
    [`(,e1 ,e2) 
     (cond [(value? e1)
	    (cond [(value? e2)
		   (cons ctx `(,e1 ,e2))]
		  [else
		   (decompose e2 (cons `(,e1 [-]) ctx))])]
	   [else
	    (decompose e1 (cons `([-] ,e2) ctx))])]
    [else (error 'decompose "unmatched ~s" e)]
    ))

(define (step e type-env)
  (match (decompose e '())
    [`(,ctx . ,redex)
      (cond [(value? redex) ;; is this really necessary?
	     (values redex type-env)]
	    [else
             (define-values (contractum type-env^) (reduce redex type-env))
	     (match contractum
		    [`(blame ,p)
                     (values `(blame ,p) type-env^)]
		    [else
		     (values (plug ctx contractum) type-env^)]
		    )])]
     ))

(define multi-step
  (lambda (e log-file type-env)
    (type-check e type-env)
    (cond [(value? e) 
	   e]
	  [else
           (define-values (res type-env^) (step e type-env))
	   (match res
	      [`(blame ,p)
	       (write-string (string-append "\\longmapsto &\\;"
					    "\\mathbf{blame}\\," 
					    (blame->string p))
			     log-file)
	       `(blame ,p)]
	      [e^
	       (write-string "\\longmapsto &\\;" log-file)
	       (write-string (print-term e^) log-file)
	       (write-string "\\\\ \n" log-file)
	       (multi-step e^ log-file type-env^)])]
	  )))

(define (run surface-prog file-name)
  (define-values (prog type) (cast-insert-term surface-prog '()))
  (call-with-output-file file-name #:exists 'replace
    (lambda (out-file)
      (write-string "\\documentclass{article}\n" out-file)
      (write-string "\\usepackage{amsmath}\n" out-file)
      (write-string "\\usepackage{fullpage}\n" out-file)
      (write-string "\\allowdisplaybreaks\n" out-file)
      (write-string "\\begin{document}\n" out-file)
      (write-string "\\tiny\\begin{align*}\n" out-file)
      (write-string (string-append "&" (print-term prog) "\\\\ \n") out-file)
      (define ret (multi-step prog out-file (empty-alist)))
      (write-string "\\end{align*}\n" out-file)
      (write-string "\\end{document}\n" out-file)
      ret
      )))

(define Id '(All X (lambda [x : X] x)))

(define p0 `((inst ,Id int L1) 42 L2))

(assert "test p0" (equal? 42 (run p0 "./p0.tex")))

(define p1
  `((lambda [x : int] x)
    ((lambda [f : (-> * *)] (f 42 L2))
     ,Id L1)
    L3))

(assert "test p1" (equal? 42 (run p1 "./p1.tex")))

(define p2
  `((lambda [f : (all X (-> X X))]
      ((inst f int L3) 42 L1))
    (lambda [x : *] x) L2))

(assert "test p2" (equal? 42 (run p2 "./p2.tex")))

(define (cast e A L)
  `((lambda [x : ,A] x)
    ,e ,L))

(define p3
  `((lambda [f : (all X (-> X X))]
      ((inst f int L1) 42 L2))
    (lambda [x : *]
      ,(cast (cast 'x 'int 'L3) '* 'L4))
    L5))

(assert "test p3" (equal? '(blame L3) (run p3 "./p3.tex")))

(define p4
  `((inst ,(cast (cast Id '(-> * *) 'L1)
                 '(all Y (-> Y Y)) 'L2)
          int L3)
    42 L4))

(assert "test p4" (equal? 42 (run p4 "./p4.tex")))

(define K `(All X (All Y (lambda [x : X] (lambda [y : Y] x)))))
(define p5
  `(((inst (inst ,(cast (cast K '(-> * (-> * *)) 'L1)
                        '(all X (all Y (-> X (-> Y Y)))) 'L2)
                 int L3)
           int L4)
    42 L5)
    0 L6))

(assert "test p5" (equal? '(blame L2) (run p5 "./p5.tex")))

(define p6
  `(((inst (inst ,(cast (cast K '(-> * (-> * *)) 'L1)
                        '(all X (all Y (-> X (-> Y X)))) 'L2)
                 int L3)
           int L4)
    42 L5)
    0 L6))

(assert "test p6" (equal? 42 (run p6 "./p6.tex")))

(define (term-precision e1 e2 type-env1 type-env2 tv-rel)
  (printf "term-precision?\n\t~a\n\t~a\n" e1 e2)
  (define-values (A1 A2)
  (match* (e1 e2)
     [((? sym?) (? sym?))
      (define t1 (dict-ref type-env1 e1))
      (define t2 (dict-ref type-env2 e2))
      (if (less-precise? (set) t1 t2 tv-rel)
          (void)
          (error 'term-precision "var less precise"))
      (values t1 t2)]
     [((? integer?) (? integer?))
      (values 'int 'int)]
     [((? boolean?) (? boolean?))
      (values 'bool 'bool)]
     [(`(let (,x1 ,rhs1) ,body1) `(let (,x2 ,rhs2) ,body2)) 
      (define-values (A1 A2) (term-precision rhs1 rhs2 type-env1 type-env2 tv-rel))
      (if (less-precise? (set) A1 A2 tv-rel)
          (void)
          (error 'term-precision "let less precise"))
      (define-values (B1 B2) (term-precision body1 body2
                                             (extend type-env1 x1 A1)
                                             (extend type-env2 x2 A2) tv-rel))
      (if (less-precise? (set) B1 B2 tv-rel)
          (void)
          (error term-precision "let less precise"))
      (values B1 B2)]
     [(`(lambda [,x1 : ,A1] ,e1) `(lambda [,x2 : ,A2] ,e2)) 
      (define-values (B1 B2) (term-precision e1 e2
                                             (extend type-env1 x1 A1)
                                             (extend type-env2 x2 A2)
                                             tv-rel))
      (if (less-precise? (set) A1 A2 tv-rel)
          (void)
          (error 'term-prec "lambda param less precise"))
      (if (less-precise? (set) B1 B2 tv-rel)
          (void)
          (error 'term-prec "lambda return less precise"))
      (values `(-> ,A1 ,B1) `(-> ,A2 ,B2))]
     [(`(All ,X1 ,e1) `(All ,X2 ,e2))
      (dict-set! tv-rel X1 X2)
      (define-values (A1 A2) (term-precision e1 e2 type-env1 type-env2 tv-rel))
      (if (less-precise? (set) `(all ,X1 ,A1) `(all ,X2 ,A2) tv-rel)
          (void)
          (error 'term-prec "big lambda less precise"))
      (values `(all ,X1 ,A1) `(all ,X2 ,A2))]
     [(`(prim ,op1 ,es1 ...) `(prim ,op2 ,es2 ...))
      (define-values (ts1 ts2) (for/lists (t1 t2) ([e1 es1] [e2 es2])
                                          (term-precision e1 e2 type-env1 type-env2
                                                          tv-rel)))
      (for/list ([t1 ts1] [t2 ts2])
                (assert "prim arg less precise" (less-precise? (set) t1 t2 tv-rel)))
      (if (less-precise? (set) (return-type op1) (return-type op2) tv-rel)
          (void)
          (error 'term-prec "prim return less precise"))
      (values (return-type op1) (return-type op2))]
     [(`(inst ,e1 ,A1) `(inst ,e2 ,A2))
      (if (less-precise? (set) A1 A2 tv-rel)
          (void)
          (error 'term-precision "inst type arg ~a <= ~a" A1 A2))
      (define-values (B1 B2) (term-precision e1 e2 type-env1 type-env2 tv-rel))
      (match* (B1 B2)
         [(`(all ,X1 ,B1^) `(all ,X2 ,B2^))
                     (display "term-prec inst 3")(newline)
          (values (type-subst B1^ X1 A1) (type-subst B2^ X2 A2))]
         [(B1 B2)
          (error 'term-precision "inst expected an all, not ~a and ~a" B1 B2)])]
     [(`(nu ,X1 ,A1 ,e1) `(nu ,X2 ,A2 ,e2))
      (if (less-precise? (set) A1 A2 tv-rel)
          (void)
          (error 'term-prec "nu RHS less precise"))
      (dict-set! tv-rel X1 X2)
      (define-values (B1 B2) (term-precision e1 e2
                                             (extend type-env1 X1 A1)
                                             (extend type-env2 X2 A2)
                                             tv-rel))
      (values B1 B2)]
     [(`(cast ,e1 ,c1) `(cast ,e2 ,c2))
      (define-values (A1 A2) (term-precision e1 e2 type-env1 type-env2 tv-rel))
      (define-values (A1^ B1) (type-check-coercion c1 type-env1))
      (define-values (A2^ B2) (type-check-coercion c2 type-env2))
      (if (less-precise? (set) A1^ A2^ tv-rel)
          (void)
          (error 'term-prec "cast source less precise"))
      (if (less-precise? (set) B1 B2 tv-rel)
          (void)
          (error 'term-prec "cast target less precise"))
      (values B1 B2)]
     [(`(,rator1 ,rand1) `(,rator2 ,rand2))
      (define-values (F1 F2) (term-precision rator1 rator2 type-env1 type-env2 tv-rel))
      (define-values (A1 A2) (term-precision rand1 rand2 type-env1 type-env2 tv-rel))
      (match* (F1 F2)
         [(`(-> ,A1^ ,B1) `(-> ,A2^ ,B2))
          (values B1 B2)]
         [(F1 F2)
          (error 'term-precision "expected a function, not ~a AND ~a" F1 F2)])]
     [(e1 e2)
      (error 'term-precision "unmatched ~s <= ~s" e1 e2)]
     ))
  (printf "term-precision\n\t~a\n<=\n\t~a\n\t= ~a , ~a\n" e1 e2 A1 A2)
  (values A1 A2))

(define (less-precise-term? cc1 cc2 type-env1 type-env2 tv-rel)
  (with-handlers
   ([exn:fail? (lambda (exn)
                 (printf "term-precision\n\t~a\n<=\n\t~a\n\t= ~a\n" cc1 cc2 #f)
                 (printf "error: ~a\n" exn)
                 #f)])
   (define-values (A1 A2)
     (term-precision cc1 cc2 type-env1 type-env2 tv-rel))
   #t))

(define (catchup cc2 type-env2 cc1 type-env1 tv-rel)
  (cond [(less-precise-term? cc1 cc2 type-env1 type-env2 tv-rel)
         (printf "in sync: ~a <= ~a\n" cc1 cc2)
         (values cc2 type-env2)]
        [(value? cc2)
         (error 'catchup "failed to catch up with: ~a" cc1)]
        [(blame? cc2)
         (error 'catchup "failed to catch up with: ~a" cc1)]
        [else
         (define-values (cc2^ type-env2^) (step cc2 type-env2))
         (printf "step2: ~a\n-----> ~a\nin: ~a\n" cc2 cc2^ type-env2^)
         (catchup cc2^ type-env2^ cc1 type-env1 tv-rel)]))

(define (sim cc1 cc2 type-env1 type-env2 tv-rel)
  (printf "*** sim: ~a <= ~a\n" cc1 cc2)
  (cond [(value? cc1)
         (define-values (cc2^ type-env2^) (catchup cc2 type-env2 cc1 type-env1 tv-rel))
         (value? cc2^)]
        [(blame? cc1)
         (define-values (cc2^ type-env2^) (catchup cc2 type-env2 cc1 type-env1 tv-rel))
         (blame? cc2^)]
        [else
         (define-values (cc1^ type-env1^) (step cc1 type-env1))
         (printf "step1: ~a\n-----> ~a\nin: ~a\n" cc1 cc1^ type-env1^)
         (define-values (cc2^ type-env2^) (catchup cc2 type-env2 cc1^ type-env1^ tv-rel))
         (sim cc1^ cc2^ type-env1^ type-env2^ tv-rel)]))

(define (run-sim grad1 grad2)
  (define-values (cc1 type1) (cast-insert-term grad1 '()))
  (define-values (cc2 type2) (cast-insert-term grad2 '()))
  (sim cc1 cc2 '() '() (make-hash)))

(assert "sim1" (run-sim p0 p0))
