#lang racket

(require racket/hash
         racket/struct
         threading
         json
         (for-syntax syntax/parse))

(struct rule
  (var guard action)
  #:transparent
  #:methods gen:custom-write
  [(define write-proc
     (make-constructor-style-printer
      (lambda (obj) 'rule)
      (lambda (obj)
        (if (eq? (rule-guard obj) #t)
            (list (rule-var obj) '= (rule-action obj))
            (list (rule-var obj) '= (rule-guard obj) '? (rule-action obj))))))])

;; creates a namespace from map from variables to values
(define (store->namespace store)
  (define ns (make-base-namespace))

  (namespace-attach-module (current-namespace) 'racket/list ns)
  (namespace-require 'racket/list ns)

  (hash-for-each store
                 (lambda (k v)
                   (namespace-set-variable-value! k v #t ns)))

  (namespace-set-variable-value! '= (lambda (a b) (if (= a b) 1 0)) #t ns)
  (namespace-set-variable-value! '!= (lambda (a b) (if (= a b) 0 1)) #t ns)
  (namespace-set-variable-value! '< (lambda (a b) (if (< a b) 1 0)) #t ns)
  (namespace-set-variable-value! '> (lambda (a b) (if (> a b) 1 0)) #t ns)
  (namespace-set-variable-value! '<= (lambda (a b) (if (<= a b) 1 0)) #t ns)
  (namespace-set-variable-value! '>= (lambda (a b) (if (>= a b) 1 0)) #t ns)
  (namespace-set-variable-value! 'if (lambda (c t f) (if (= c 1) t f)) #t ns)
  (namespace-set-variable-value! 'not (lambda (b) (if (= b 1) 0 1)) #t ns)
  (namespace-set-variable-value! 'and (lambda (a b) (if (and (= a 1) (= b 1)) 1 0)) #t ns)
  (namespace-set-variable-value! 'or (lambda (a b) (if (or (= a 1) (= b 1)) 1 0)) #t ns)

  (namespace-set-variable-value! '>> (lambda (o n) (arithmetic-shift o (- n))) #t ns)
  (namespace-set-variable-value! '<< (lambda (o n) (arithmetic-shift o n)) #t ns)
  (namespace-set-variable-value! '& (lambda (a b) (bitwise-and a b)) #t ns)
  (namespace-set-variable-value! '|| (lambda (a b) (bitwise-ior a b)) #t ns)
  (namespace-set-variable-value! '^ (lambda (a b) (bitwise-xor a b)) #t ns)

  ns)

;; updates a store given a group
(define (update var-store group)
  ;; create namespace for evaluating rule actions
  ;; (println (~a 'update var-store))
  (define ns (store->namespace var-store))

  (define updated-this-cycle (list))

  ;; fold actions applied to the old store into the new store
  (define r (foldl
             (lambda (rule store)
               (let ([var (rule-var rule)]
                     [f (rule-action rule)]
                     [guard (rule-guard rule)])
                 (if (or (eq? (eval guard ns) #t) (= (eval guard ns) 1))
                     (begin
                       (set! updated-this-cycle (cons var updated-this-cycle))
                       (hash-set store var (eval f ns)))
                     store)))
             var-store
             group))

  ;; make sure that we didn't update the same variable twice
  (let ([dup (check-duplicates updated-this-cycle)])
    (when dup
      (pretty-print var-store)
      (raise (~a "Duplicate Update: " dup))))

  r)

;; group syntax
(define-syntax (group stx)
  ;; syntax class that makes the guard optional
  (define-syntax-class rule-defn
    #:description "rule definition"
    #:attributes (var guard rhs)
    (pattern [(var idx) expr]
             #:with guard #'#t
             #:with rhs #'(list-set var idx expr))
    (pattern [(var idx) guard expr]
             #:with rhs #'(list-set var idx expr))
    (pattern [var rhs]
             #:with guard #'#t)
    (pattern [var guard rhs]))

  (syntax-parse stx
    [(_ r:rule-defn ...)
     #'(list (rule 'r.var 'r.guard 'r.rhs) ...)]))

;; runs `update` until `var-store[done] == 1` and then returns the store
(define ((enable group [should-print? #f]) store)
  (when should-print?
    (pretty-print (should-print? store))
    ;; (read-line)
    )
  (cond [(and (hash-has-key? store 'done)
              (= (hash-ref store 'done) 1))
         ;; XXX(probably remove this at some point)
         (hash-set store 'done 0)]
        [else
         (begin
           ((enable group should-print?) (update store group)))]))

(define-syntax-rule (seq A B ...)
  (lambda (store)
    (~> (A store)
        (B _) ...)))

(define ((c-if var C T F) store)
  (define s-p ((enable C) store))
  (if (= (hash-ref s-p var) 1)
      (T s-p)
      (F s-p)))

(define ((c-while var C B) store)
  ;; (println 'waiting...)
  ;; (read-line (current-input-port) 'any)
  (define s-p ((enable C) store))
  (if (= (hash-ref s-p var) 1)
      ((c-while var C B) (B s-p))
      s-p))

(define (get-rule v G)
  (findf (lambda (x) (eq? v (rule-var x))) G))

(define (get-rules v G)
  (filter (lambda (x) (eq? v (rule-var x))) G))

;; insert a `go` guard for each rule in group G
(define (go-ify G [go-name 'go])
  (map (lambda (r)
         (if (eq? (rule-guard r) #t)
             (struct-copy rule r
                          [guard go-name])
             (struct-copy rule r
                          [guard `(and ,go-name ,(rule-guard r))])))
       G))

;; substitute all instances of x for v in rule G
(define (substitute G x v)
  (define (replace-in L)
    (cond [(list? L) (map (lambda (sym) (if (eq? sym x) v sym)) L)]
          [(eq? L x) v]
          [else L]))
  (map (lambda (r)
         (struct-copy rule r
                      [guard (replace-in (rule-guard r))]
                      [action (replace-in (rule-action r))]))
       G))

;; combines two groups into 1, removing the done signal
(define-syntax-rule (union A ...)
  (set-union
   (set-remove A (get-rule 'done A))
   ...))

(define (compose-seq G holes [state-sym 'state])
  (let* ([l (sub1 (length holes))]
         [G-p (foldl (lambda (go-sym acc)
                       (cons (substitute (car acc) (car go-sym) `(= ,state-sym ,(cdr acc)))
                             (add1 (cdr acc))))
                     (cons G 0)
                     holes)]
         [state-ups (foldl (lambda (done-rule acc)
                             (cons (cons (rule state-sym
                                               (if (eq? (rule-guard (cdr done-rule)) #t)
                                                   `(= ,state-sym ,(cdr acc))
                                                   `(and ,(rule-guard (cdr done-rule))
                                                         (= ,state-sym ,(cdr acc))))
                                               (modulo (add1 (cdr acc)) (+ 2 l)))
                                         (car acc))
                                   (add1 (cdr acc))))
                           (cons (list) 0)
                           holes)])
    (append (car G-p)
            (car state-ups)
            (list
             (rule state-sym `(= ,state-sym ,(+ 1 l)) 0)
             (rule 'done `(= ,state-sym ,(add1 l)) 1)))))

(define input
  (read-json (open-input-file "input.data")))

(define store
  (make-immutable-hash
   `((done . 0)
     (real . ,(hash-ref input 'real))
     (img . ,(hash-ref input 'img))
     (real_twid . ,(hash-ref input 'real_twid))
     (img_twid . ,(hash-ref input 'img_twid))
     (span . 0)
     (log . 0)
     (odd . 0)
     (even . 0)
     (real_odd . 0)
     (img_odd . 0)
     (real_even . 0)
     (img_even . 0)
     (temp_r . 0)
     (temp_i . 0)
     (rootindex . 0)
     (temp . 0)

     (c1 . 0)
     (c2 . 0)
     (c3 . 0))))

;; let span = 32 >> 1
;; let log = 0
(define Init
  (group
   [span (>> 32 1)]
   [log 0]
   [done 1]))

;; span != 0
(define WhileCond-1
  (group
   [c1 (!= span 0)]
   [done 1]))

;; let odd = span
(define Loop1Expr1
  (group
   [odd span]
   [done 1]))

;; odd < 32
(define WhileCond-2
  (group
   [c2 (< odd 32)]
   [done 1]))

;; odd := odd | span;
;; let real_odd = real[odd];
;; let img_odd = img[odd];
(define Loop2E1
  (group
   [odd (|| odd span)]
   [real_odd (list-ref real (|| odd span))]
   [img_odd (list-ref img (|| odd span))]
   [done 1]))

;; let even = odd ^ span;
;; let real_even = real[even];
;; let img_even = img[even];
(define Loop2E2
  (group
   [even (^ odd span)]
   [real_even (list-ref real (^ odd span))]
   [img_even (list-ref img (^ odd span))]
   [done 1]))

;; let temp_r = real_even + real_odd;
;; let temp_i = img_even + img_odd;
;; real[odd] := real_even - real_odd;
;; img[odd] := img_even - img_odd;
(define Loop2E3
  (group
   [temp_r (+ real_even real_odd)]
   [temp_i (+ img_even img_odd)]
   [(real odd) (- real_even real_odd)]
   [(img odd) (- img_even img_odd)]
   [done 1]))

;; real[even] := temp_r;
;; img[even] := temp_i;
;; let rootindex = (even << log) & (1024 - 1);
(define Loop2E4
  (group
   [(real even) temp_r]
   [(img even) temp_i]
   [rootindex (& (<< even log) (- 32 1))]
   [done 1]))

;; if (rootindex != 0)
(define IfCond
  (group
   [c3 (!= rootindex 0)]
   [done 1]))

;;    let temp = real_twid[rootindex] * real[odd] - img_twid[rootindex] * img[odd];
;;    img_odd := img[odd];
(define IfE1
  (group
   [temp (- (* (list-ref real_twid rootindex) (list-ref real odd))
            (* (list-ref img_twid rootindex) (list-ref img odd)))]
   [img_odd (list-ref img odd)]
   [done 1]))

;;    img[odd] := real_twid[rootindex] * img_odd + img_twid[rootindex] * real[odd];
(define IfE2
  (group
   [(img odd) (+ (* (list-ref real_twid rootindex) img_odd)
                 (* (list-ref img_twid rootindex) (list-ref real odd)))]
   [done 1]))

;;    real[odd] := temp;
(define IfE3
  (group
   [(real odd) temp]
   [done 1]))

;; odd := odd + 1;
(define Loop2E6
  (group
   [odd (+ odd 1)]
   [done 1]))

;; span := span >> 1
;; log := log + 1
(define Loop1Expr2
  (group
   [span (>> span 1)]
   [log (+ log 1)]
   [done 1]))

(define ((dbg-msg s) x)
  (println s)
  x)

(define ((dbg-sym sym) x)
  (println (~a sym '= (hash-ref x sym)))
  x)

(define (pause x)
  (read-line)
  x)

;; (define control
;;   (seq (enable Init)
;;        (c-while 'c1 WhileCond-1
;;                 (seq (dbg-msg "=== starting outer ===")
;;                      (dbg-val 'span)
;;                      (enable Loop1Expr1)
;;                      (c-while 'c2 WhileCond-2
;;                               (seq (dbg-msg "--- starting inner ---")
;;                                    (dbg-val 'odd)
;;                                    (dbg-val 'span)
;;                                    (enable Loop2E1)
;;                                    (dbg-val 'odd)
;;                                    (enable Loop2E2)
;;                                    (enable Loop2E3)
;;                                    (enable Loop2E4)
;;                                    (dbg-val 'even)
;;                                    (dbg-val 'log)
;;                                    (dbg-val 'rootindex)
;;                                    (c-if 'c3 IfCond
;;                                          (seq (dbg-msg "cond: true")
;;                                               (enable IfE1)
;;                                               (enable IfE2)
;;                                               (enable IfE3))
;;                                          (dbg-msg "cond: false"))
;;                                    (dbg-val 'odd)
;;                                    (enable Loop2E6)))
;;                      (enable Loop1Expr2)))))

(define control
  (seq (enable Init)
       (c-while 'c1 WhileCond-1
                (seq (dbg-sym 'span)
                     (enable Loop1Expr1)
                     (c-while 'c2 WhileCond-2
                              (seq (lambda (x) (pretty-print x) x)
                                   (enable Loop2E1)
                                   (enable Loop2E2)
                                   (enable Loop2E3)
                                   (enable Loop2E4)
                                   (c-if 'c3 IfCond
                                         (seq (enable IfE1)
                                              (enable IfE2)
                                              (enable IfE3))
                                         (lambda (x) x))
                                   (enable Loop2E6)
                                   (lambda (x) (pretty-print x) x)))
                     (enable Loop1Expr2)))))

(define if-body
  (compose-seq (union (go-ify IfE1 'go1)
                      (go-ify IfE2 'go2)
                      (go-ify IfE3 'go3))
               `((go1 . ,(get-rule 'done IfE1))
                 (go2 . ,(get-rule 'done IfE2))
                 (go3 . ,(get-rule 'done IfE3)))
               'state1))

(define if-stmt
  (~> (union (go-ify if-body 'go-T))
      (substitute _ 'go-T (rule-action (get-rule 'c3 IfCond)))
      (append _ (list (rule 'done '(or (= rootindex 0) (= state1 2)) 1)))))

(define while2-body
  (compose-seq (union (go-ify Loop2E1 'go1)
                      (go-ify Loop2E2 'go2)
                      (go-ify Loop2E3 'go3)
                      (go-ify Loop2E4 'go4)
                      (go-ify if-stmt 'go5)
                      (go-ify Loop2E6 'go6))
               `((go1 . ,(get-rule 'done Loop2E1))
                 (go2 . ,(get-rule 'done Loop2E2))
                 (go3 . ,(get-rule 'done Loop2E3))
                 (go4 . ,(get-rule 'done Loop2E4))
                 (go5 . ,(get-rule 'done if-stmt))
                 (go6 . ,(get-rule 'done Loop2E6)))
               'state2))

(define inner-while
  (~> (union (go-ify while2-body 'go))
      (substitute _ 'go (rule-action (get-rule 'c2 WhileCond-2)))
      (append _
              (list (rule 'done `(not ,(rule-action (get-rule 'c2 WhileCond-2))) 1)))))

(define while1-body
  (compose-seq (union (go-ify Loop1Expr1 'go1)
                      (go-ify inner-while 'go2)
                      (go-ify Loop1Expr2 'go3))
               `((go1 . ,(get-rule 'done Loop1Expr1))
                 (go2 . ,(get-rule 'done inner-while))
                 (go3 . ,(get-rule 'done Loop1Expr2)))
               'state3))

(define outer-while
  (~> (union (go-ify while1-body 'go))
      (substitute _ 'go (rule-action (get-rule 'c1 WhileCond-1)))
      (append _
              (list (rule 'done `(not ,(rule-action (get-rule 'c1 WhileCond-1))) 1)))))

(define compiled-control
  (enable (compose-seq (union (go-ify Init 'go1)
                              (go-ify outer-while 'go2))
                       `((go1 . ,(get-rule 'done Init))
                         (go2 . ,(get-rule 'done outer-while)))
                       'state4)))

(define r (compiled-control (~> (hash-set store 'state1 0)
                                (hash-set _ 'state2 0)
                                (hash-set _ 'state3 0)
                                (hash-set _ 'state4 0))))
(define (cmp s t)
  (andmap
   (lambda (a b) (< (abs (- a b)) 0.01))
   (hash-ref r s)
   (hash-ref input t)))
(and
 (cmp 'real 'gold_real)
 (cmp 'img 'gold_img)
 (cmp 'real_twid 'gold_real_twid)
 (cmp 'img_twid 'gold_img_twid))
