(ns dpl.core
  (:use clojure.core))

;;;Utils
(defn get-niled-sym [x] (if (symbol? x) (symbol (name x)) x))
(defn fevery? "Checks if thing satisfies all the predicates in conds"
  [conds thing] 
  (every? #(apply % (list thing)) conds))
(defn sym= [x y] (if (and (symbol? x) (symbol? y)) (= (name x) (name y))))
(defmacro lif [x y]
  `(cond (not ~x) true
         ~y true
         true false))
;;
;; Things in the underlying logical world.
;;
(def *fancy-syntax*
  ^{:doc "A map for mapping connectives to unicode symbols for beautifully printing out formulae to the REPL."
    :private true}
  {:if '⇨  :and '∧ :or '∨ :not '¬ :iff '⇔ })

(defrecord error [deduction])
(defrecord dpl-method [name body function])
(defprotocol proposition )
(defprotocol atomic )
(defprotocol compound)
(defrecord atomic-proposition [value syntax] proposition atomic)
(defrecord compound-proposition [connective subs syntax] proposition compound)
(defn proposition? [x] (satisfies? proposition x))
(defn atomic-proposition? [x] (satisfies? atomic x))
(defn compound-proposition? [x] (satisfies? compound x))

;;;
;;; Logical and non-logical signature handling
;;;
(def logical-signature 
  (atom #{'(or -1) '(and -1) '(if 2) '(iff 2) '(not 1)}
        :validator
        (fn [x] (and (set? x)
                     (every?
                      (fn [y] (and (symbol? (first y))
                                   (fevery? (list integer? #(>= % -1))
                                            (second  y))))
                      x)))))

(def non-logical-signature
  (atom
   #{'True 'False}
   :validator #(and (set? %) (every? symbol? %))))

(defmacro  add-to-signature [definition type]
  `(reset! ~type (conj (deref ~type) '~definition)))

(defmacro declare-propositions [& props]
  (cons 'do (map  #(list 'add-to-signature % 'non-logical-signature) props)))
;;;
;;; Handling assumption bases
;;;

(def *dpl-trace-on* false)
(defn  dpl-trace [] (alter-var-root   (var *dpl-trace-on*)  #(if % false true)))

(def *assumption-base*  #{})

(set-validator! (var *assumption-base*)  (fn [x] (if *dpl-trace-on* (println "Current assumption base" x))
                                           (every? proposition? x)))

(defn assert! [prop] (pr prop) (alter-var-root  (var *assumption-base*) clojure.set/union #{prop}))

(defn ab []  @*assumption-base*)

(defn print-AB []
  (doall
   (map
    #(print %2 ": " %1 (str "\n----------\n"))
    @*assumption-base* (range 1 (+ 1 (count (ab)))))) nil)

(defn reset-assumption-base []
  (alter-var-root (var *assumption-base*)  (fn [x] {})))

;;;
;;; Parsing input formulae
;;;
(defmacro validate [form message]
  `(if ~form
    true
    (throw (new Exception (str ~message)))))

(defn validate-logical [x]
  (some (fn [y]
          (and (sym= (first y) (get-niled-sym (first x)))
               (or (= (second y) -1)
                   (= (second y) (- (count x) 1)))))
        @logical-signature))
(defn validate-compound [inp]
  (letfn  []
    (and
     (validate
      (validate-logical inp)
      (str  "Logical signature mistake " inp))
     (validate (every? #(or (if (not (symbol? %)) (validate-logical %))
                            (@non-logical-signature (get-niled-sym %))
                            (proposition? %)) (rest inp))
               (str "Non-logical signature mistake " inp)))))


(defn parse-wff [thing]
  (cond (proposition? thing) thing
        (if (symbol? thing) (@non-logical-signature (get-niled-sym thing)))
        (atomic-proposition. (keyword (symbol (name thing))) (get-niled-sym thing))
        (if (symbol? thing) (not (@non-logical-signature (get-niled-sym thing))))
        (throw
         (new Exception
              (str "Symbol "
                   thing
                   " not in the non-logical signature.\nAdd it to the signature with: (add-to-signature "
                   thing " non-logical-signature)")))
        (validate-compound thing) (compound-proposition. (get-niled-sym (first thing))
                                                         (map parse-wff (rest thing))
                                                         (*fancy-syntax* (keyword (name (first thing)))))))
(defn $ [wff] (parse-wff wff))

(defmethod print-method dpl-method  [o, w]
  (.write w "[DPL Primitive Method: ")
  (print-method (:name o) w)
  (print-method (:function o) w)
  (.write w "]"))

(defmethod print-method error  [o, w]
  (print-method  '▼ w))

(defmethod print-method atomic-proposition  [o, w]
  (.write w (str (:syntax o))))

(defmethod print-method compound-proposition  [o, w]
  (if (sym= 'not (:connective o))
    (do (.write w (str (:syntax o)))
        (if (or (atomic-proposition? (first (:subs o)))
                (sym= 'not (:connective (first ( :subs o)))))
          (print-method (first (:subs o)) w)
          (do (.write w (str "(")) (print-method (first (:subs o)) w) (.write w (str ")")))))
    (doall (map #(if (proposition? %)
                   (if (or  (atomic-proposition? %) (sym= 'not (:connective % )))
                     (print-method %  w)
                     (do (.write w (str "(")) (print-method % w) (.write w ( str ")"))))
                   (.write w (str " " % " ")))
                (interpose (:syntax o) (:subs o))))))

;;;
;;; Defining Primitive methods
;;;
(def $primitive-methods$
  (atom {} :validate (fn [x] (every? #(and (symbol (first %)) (symbol (second %))) (seq x)))))

(defn create-internal-dpl-method-definition [name args body]
  `(defn ~name ~args
    (letfn [(internal# [] ~@body)] 
      (let [result# (internal#)]
        (if (proposition? result#)
          result#
          (throw (new Exception "Error in method definition. Output not a proposition")))))))

(defmacro define-primitive-method [method-name args & body]
  (let [dpl-m-name (gensym (str "dpl-internal-method-" method-name))]
    `(let [dmethod# (dpl-method. '~method-name
                                 (list (into [] '~args) '~@body)
                                 '~dpl-m-name)]
      (reset! $primitive-methods$ (conj @$primitive-methods$
                                        {(name  '~method-name) dmethod#}))
      ~(create-internal-dpl-method-definition dpl-m-name  args body)
      dmethod#)))

(defn unification-error [x y bindings message]
  (throw (new Exception (str "Can't unify " x " and " (print-str y) " with bindings " bindings  ".\n" message))))

(defn unify [pattern form bindings]
  (letfn [(bind-atomic []
            (let [current-value (bindings pattern)]
              (if (lif current-value (= current-value form)) 
                {pattern form}
                (unification-error pattern form bindings "Binding value clash error."))))]
    (cond (not (or  (lif (atomic-proposition? form) (symbol? pattern))
                    (and (list?  pattern) (compound-proposition? form)
                         (sym= (first pattern) (:connective form)))))
          (unification-error pattern form bindings "Type mismatch error.")
          (symbol? pattern) (merge bindings (bind-atomic))
          (and (list? pattern) (compound-proposition? form))
          (apply merge (cons bindings (map #(unify %1 %2 bindings) (rest pattern) (:subs form)))))))


(defn bindings-to-arg-list [patterns forms]
  (reduce
   #(merge %1 (first %2) (second %2))
   (seq
    (apply merge-with
           #(if (not (= %1 %2))
              (throw (new Exception (str "Inconsistent bindings " (print-str  %1) " and " (print-str %2))))
              %1)
           (map #(unify %1 %2 {}) patterns forms)))))


(defn match-patterns [patterns forms]
  (apply merge-with
         #(if (not (= %1 %2))
            (throw (new Exception (str "Inconsistent bindings " (print-str  %1) " and " (print-str %2))))
            %1)
         (map #(unify %1 %2 {}) patterns forms)))

(defn vars [pattern]
  (if (or (symbol? pattern) (empty? pattern) )
    pattern
    (map vars (rest pattern))))

(defmacro letp [[& bindings] & body]
  (let [patterns (take-nth 2 bindings)
        forms (take-nth 2 (rest bindings))
        pvars (flatten (map vars patterns))]
    `(apply (fn ~(into [] pvars) ~@body)
            (map (match-patterns '~patterns (list ~@forms)) '~pvars))))

;;;
;;; Type-α Propositional DPL Interpreter
;;;
(defmacro with-appended-assumption-base [ab & body]
  `(binding [*assumption-base* (clojure.set/union ~ab *assumption-base*)]
     ~@body))

(defn dpl-interpreter [deduction]
 (if *dpl-trace-on* (do (println ) (println "["deduction"]")))
  (let [ded-name (name (first deduction))
        primitive-method (:function (@$primitive-methods$ ded-name))]
    (cond
     primitive-method (apply (eval primitive-method) (rest deduction))
     (= ded-name "assume")
     (with-appended-assumption-base #{(second deduction)}
       ($ (list 'if (second deduction) (dpl-interpreter (last deduction)))))
     (= ded-name "compose")
     (with-appended-assumption-base #{(dpl-interpreter (second deduction))}
       (dpl-interpreter (last deduction)))
     (= ded-name "assume-all")
     (with-appended-assumption-base (set (butlast (rest deduction)))
       ($(reduce (fn [x y] (list 'if y x)) (dpl-interpreter (last deduction))
                 (reverse (butlast (rest deduction))))))
     (= ded-name "compose-all")
     (with-appended-assumption-base #{(dpl-interpreter (second deduction))}
       (let [next (rest (rest deduction))]
         (if (<= 2 (count next))
           (dpl-interpreter (cons 'compose-all next))
           (dpl-interpreter (first (rest (rest deduction)))))))
     true (error. deduction))))

(defn parse-deduction [deduction]
  (cons (first deduction)
        (map #(let [top-form-name (name (if (list? %) (first %) ""))]
                (if (or (@$primitive-methods$ top-form-name)
                        (#{"compose" "assume" "compose-all" "assume-all"} top-form-name))
                  (parse-deduction %)
                  ($ %)))
             (rest deduction))))

(defmacro ! [deduction] `(dpl-interpreter (parse-deduction '~deduction)))


(defn or-check [& propositions]
  (if (not (some *assumption-base* propositions))
    (throw
     (new Exception (str "Or-Check Failed " (print-str propositions) " are not in the assumption base!")))))

(defn check [proposition]
  (if (not (*assumption-base* proposition))
    (throw (new Exception (str "Check Failed: " (print-str proposition) " is not in the assumption base!")))))

;;;
;;; Primitive method definitions
;;;

(define-primitive-method claim [P]
  (check P) P)
(define-primitive-method both [P Q]
  (check P) (check Q)
  ($`(and ~P ~Q)))


(define-primitive-method modus-ponens [P1 P2]
  (letp [(if P Q) P1 P P2]
        (check P1) (check P2)
        Q))

(define-primitive-method modus-tollens [P1 P2]
  (letp [(if P Q) P1
         (not Q) P2 ]
        (check P1) (check P2)
        ($`(not ~P)))) 

(define-primitive-method both [P1 P2]
  (check P1) (check P2)
  ($`(and ~P1 ~P2)))


(define-primitive-method left-and  [P]
  (letp [(and L R) P]
        (check P) L))

(define-primitive-method right-and  [P]
  (letp [(and L R) P]
        (check P) R))

(define-primitive-method or-intro [P Q]
  (or-check P Q)
  ($ (list 'or P Q)))

(define-primitive-method or-elim [or-P left-C right-C]
  (letp [(or P1 P2) or-P
         (if P1 Q) left-C
         (if P2 Q) right-C]
        (check or-P) (check left-C) (check right-C)
        Q))

(define-primitive-method absurd [P1 P2]
  (letp [P P1
         (not P) P2]
        ($'False)))

(define-primitive-method true-intro []
  ($'True))

(define-primitive-method false-elim []
  ($'(not False)))

(define-primitive-method double-negation [P]
  (letp [(not (not Q)) P] (check P)
        Q))

(define-primitive-method equivalence [P Q]
  (letp [(if P1 P2) P
         (if P2 P1) Q]
        ($`(iff ~P1 ~P2))))

