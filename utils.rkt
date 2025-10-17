#lang racket

(provide lookup extend empty-alist assert map2 typeof-op reset-symbols gensym sym->string sym? 
	 negate write-latex blame->string sym->base)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; gensym 

(define counters (make-hash))

(define (reset-symbols)
  (set! counters (make-hash)))

(define (sym? sym)
  (or (symbol? sym)
      (and (pair? sym)
	   (symbol? (car sym))
	   (number? (cdr sym)))))

(define (sym->base sym)
  (cond [(symbol? sym) sym]
        [(pair? sym) (car sym)]))

(define (gensym sym)
  (let ([base (sym->base sym)])
    (let ([id (hash-ref! counters base 0)])
      (let ([r (cons base id)])
        (hash-set! counters base (+ id 1))
        r))))

(define (sym->string sym)
  (cond [(symbol? sym)
	 (string-append "\\mathit{" (symbol->string sym) "}")]
	[else
	 (string-append "\\mathit{" (symbol->string (car sym)) "}"
			"_{"
			(number->string (cdr sym))
			"}"
			)
	 ]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (negate phi)
  (match phi
     ['() '()]
     [`(- ,a) `(+ ,a)]
     [`(+ ,a) `(- ,a)]
     [else (error 'negate "unmatched ~a" phi)]
     ))

(define (lookup	key alist)
  (dict-ref alist key))

(define (extend alist key value)
  (dict-set alist key value))

(define (empty-alist) '())

(define assert
  (lambda (msg b)
    (if (not b)
	(begin
	  (display "ERROR: ")
	  (display msg)
	  (newline))
	(begin
	  (display "passed ")(display msg)(newline)
	  (void)))))

;; This function is like map but the function f returns
;; two values using the ``values'' form. Thus, the result
;; of map2 is two lists.
(define (map2 f ls)
  (cond [(null? ls)
         (values '() '())]
        [else
         (let-values ([(x1 x2) (f (car ls))]
                      [(ls1 ls2) (map2 f (cdr ls))])
           (values (cons x1 ls1) (cons x2 ls2)))]))

(define (typeof-op op tys)
  (match op
     ['+ 'int]
     ['- 'int]
     ['* 'int]
     [else (error 'typeof-op "unmatched ~a" op)]
     ))


(define (write-latex prog-string file-name)
  (call-with-output-file file-name #:exists 'replace
    (lambda (out-file)
      (write-string "\\documentclass{article}\n" out-file)
      (write-string "\\usepackage{amsmath}\n" out-file)
      (write-string "\\usepackage{fullpage}\n" out-file)
      (write-string "\\begin{document}\n" out-file)
      (write-string "\\[\n" out-file)
      (write-string prog-string out-file)
      (write-string "\n\\]\n" out-file)
      (write-string "\\end{document}\n" out-file)
      (void)
      )))

(define (blame->string p)
  (match p
     ['() "\\bullet"]
     [(? sym?)
      (sym->string p)]
     [`(+ ,l)
      (string-append "{+}" (sym->string l))]
     [`(- ,l)
      (string-append "{-}" (sym->string l))]
     [else
      (error 'blame->string "unmatched ~a" p)]
     ))
