#!r6rs

(library
 (crane regexp)
 (export regexp->predicate)
 (import (rnrs)
         (et_al def)
         (et_al tuple)
         (et_al loop)
         (et_al misc))

 (define transitive
   ((tuple
     ()
     ([to (lambda (v) v)]
      [predicate (lambda (v) v)])
     (to predicate))))

 (define entry
   ((tuple
     ()
     ([id
       (lambda (v)
         (if (or (symbol? v) (number? v))
             v
             (raise v)))]
      [paths
       (lambda (v)
         (if (list? v)
             v
             (raise v)))])
     (id paths))))

 ;; records: ((status next-stage-records) ... )
 (define predicate
   (tuple
    (nfa-lambda decision-mode)
    ([nfa
      nfa-lambda]
     [dfa
      (lambda () 0)]
     [nfa-traversal
      ;; TODO: Add decision processing
      (lambda ()
        (lambda (input)
          (cond
            [(symbol? nfa)
             (case nfa
               [(Epsilon)
                `(:final ,nil)])]
            [(char? nfa)
             (let ([e (input)])
               (if (eqv? nfa e)
                   `(:final ,(list e))
                   `(:cancel ,(list e))))]
            [else
             (let ([result
                    (let loop ([entry (car nfa)]
                               [p (input ':pos)])
                      (if (null? (entry 'paths))
                          nil
                          (map
                           (lambda (path)
                             (input ': p)
                             (let* ([predicate (path 'predicate)]
                                    [nfa-traversal (predicate 'nfa-traversal)]
                                    [to (car
                                         (memp
                                          (lambda (x)
                                            (eqv? (x 'id) (path 'to)))
                                          nfa))]
                                    [r (nfa-traversal input)]
                                    [n (loop to (input ':pos))])
                               (cond
                                 [(null? n)
                                  (list r n)]
                                 [(and (decision-mode r)
                                       (exists (lambda (x) (decision-mode (car x)))  n))
                                  (list r (filter (lambda (x) (decision-mode (car x))) n))]
                                 [else
                                  (list #f ()) ])))
                           (entry 'paths))))])
               (if (or (null? result)
                       (exists (lambda (x) (car x)) result))
                   `(:final ,(filter (lambda (x)
                                       (decision-mode (car x)))
                                     result))
                   `(:cancel ,nil)))])))])
    (nfa)))

 (define seq-predicate
   (predicate
    (lambda (patterns)
      (reverse
       (let loop ([e patterns]
                  [c 0]
                  [r '()])
         (cond
           [(null? e) r]
           [(null? (cdr e))
            (cons
             (entry (+ 1 c) '())
             (cons
              (entry c (list (transitive (+ 1 c) (regexp->predicate (car e)))))
              r))]
           [else
            (loop
             (cdr e)
             (+ 1 c)
             (cons
              (entry c (list (transitive (+ 1 c) (regexp->predicate (car e)))))
              r))]))))
    (lambda (status)
      (eqv? ':final (car status)))))

 (define anyof-predicate
   (predicate
    (lambda (patterns)
      (list
       (entry
        0
        (iter ([e patterns])
              :collect (r . ())
              (cons
               (transitive
                1
                (regexp->predicate e))
               r)))
       (entry 1 '())))
    (lambda (status)
      (eqv? ':final (car status)))))

 (define optional-predicate
   (predicate
    (lambda (pattern)
      (list
       (entry
        0
        (list
         (transitive 1 (regexp->predicate pattern))
         (transitive 1 Epsilon-predicate)))
       (entry 1 '())))
    (lambda (status)
      (eqv? ':final (car status)))))

 (define repeat-predicate
   (predicate
    (lambda (pattern)
      (list
       (entry 0 (list (transitive 1 (regexp->predicate pattern))))
       (entry 1 (list (transitive 0 Epsilon-predicate)
                      (transitive 2 Epsilon-predicate)))
       (entry 2 ())))
    (lambda (status)
      (eqv? ':final (car status)))))

 (define char-predicate
   (predicate
    (lambda (pattern)
      pattern)
    (lambda (status)
      (eqv? ':final (car status)))))

 (define Epsilon-predicate
   ((predicate
     (lambda (pattern)
       (list
        (entry 0 '())))
     (lambda (status)
       (eqv? ':final (car status))))
    'Epsilon))

 (define (regexp->predicate pattern)
   (letrec ([seq (lambda (patterns)
                   (seq-predicate patterns))]
            [anyof (lambda (patterns)
                     (anyof-predicate patterns))]
            [ranges (lambda (ranges)
                      (anyof
                       (iter ([e ranges])
                             :collect (r . '())
                             (let loop ([from (if (char? (car e)) (char->integer (car e)) e)]
                                        [to (if (char? (cdr e)) (char->integer (cdr e)) e)]
                                        [r r])
                               (if (>= from to)
                                   (cons (integer->char from) r)
                                   (loop (+ 1 from) to (cons (integer->char from) r)))))))]
            [optional (lambda (pattern)
                        (optional-predicate pattern))]
            [repeat (lambda (pattern)
                      (repeat-predicate pattern))]
            [char (lambda (pattern)
                    (char-predicate pattern))])
     (cond
       [(list? pattern)
        (let ([indicator
               (car pattern)]
              [arguments
               (cdr pattern)])
          (case indicator
            [(:seq)                        ; :seq patterns ...
             (seq arguments)]
            [(:anyof)                      ; :any patterns ...
             (anyof arguments)]
            ;;
            [(:ranges)                     ; :ranges (from . to) ...
             (ranges arguments)]
            [(:except)                     ; :except patterns ...
             'todo]
            ;;
            [(:optional)                   ; :optional pattern
             (when (null? (cdr arguments))
               (optional (car arguments)))]
            [(:repeat)                     ; :repeat pattern
             (when (null? (cdr arguments))
               (repeat (car arguments)))]
            ;;
            [(:times)                      ; :times most least pattern
             'todo]
            [(:most)                       ; :most times pattern
             'todo]
            [(:least)                      ; :least times pattern
             'todo]
            ;;
            [(:select)                     ; :select pattern path ; path => shortest, longest, n
             'todo]
            [(:match)                      ; :match lambda
             'todo]
            ;;
            [(:assert)                     ; :assert pattern
             'todo]
            ;;
            [(:exist)                      ; :exist patterns ...
             'todo]
            [(:none)                       ; :none patterns ...
             'todo]))]
       [(string? pattern)
        (seq (string->list pattern))]
       [(number? pattern)
        pattern]
       [(symbol? pattern)
        (case pattern
          [(EOF) 'eof]
          [(BOF) 'bof]
          [(EOL) 'eol]
          [(BOL) 'bol]
          [(Epsilon) Epsilon-predicate]
          [(Blank) 'Blank]
          [(Space) 'Space]
          [(Return) 'CarriageReturn]
          [(Newline) 'Linefeed]
          [(Digit) 'Digits]
          [(Alphabetic) 'Digits]
          [(Any) 'Any])]
       [(char? pattern)
        (char pattern)])))

 ;; Debug utilities

 (define display-nfa-tree
   (lambda (predicate)
     (letrec ([helper
               (lambda (predicate l)
                 (cond
                   [(char? (predicate 'nfa))
                    (times l (display "|\t"))
                    (display "char: ")
                    (display (predicate 'nfa))
                    (display "\n")]
                   [(symbol? (predicate 'nfa))
                    (times l (display "|\t"))
                    (display "symbol: ")
                    (display (predicate 'nfa))
                    (display "\n")]
                   [else
                    (let ([entries (predicate 'nfa)])
                      (times l (display "|\t"))
                      (display "graph:\n")
                      (iter ([entry entries])
                            (let ([id (entry 'id)]
                                  [paths (entry 'paths)])
                              (times l (display "|\t"))
                              (display "id: ")
                              (display id)
                              (display ";\n")
                              (iter ([path paths])
                                    (let ([to (path 'to)]
                                          [predicate (path 'predicate)])
                                      (times l (display "|\t"))
                                      (display "|\tto: ")
                                      (display to)
                                      (display ";\n")
                                      (helper predicate (+ 1 l)))))))]))])
       (helper predicate 0))))

 (define print-log
   (lambda args
     (for-each
      display
      args)))

 (define (string-engine str)
   (let ([str str]
         [p -1])
     (lambda args
       (cond
         [(eqv? 0 (length args))
          (set! p (+ p 1))
          (string-ref str p)]
         [(and (eqv? 2 (length args))
               (eqv? ': (car args))
               (number? (cadr args)))
          (set! p (cadr args))]
         [(and (eqv? 1 (length args))
               (eqv? ':pos (car args)))
          p]))))

 )
