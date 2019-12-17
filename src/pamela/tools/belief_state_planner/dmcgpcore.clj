;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.dmcgpcore
  "Intermediate Representation Extraction"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [environ.core :refer [env]]
            [clojure.data.xml :as xml]
            [clojure.data.csv :as csv]
            [clojure.java.io :as io]
            [clojure.data.json :as json]
            [pamela.tools.belief-state-planner.runtimemodel :as rtm]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.expressions :as dxp]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.dmcgpcore)

(defrecord MethodQuery [pclass methodsig rootobject rto])

(def ^:dynamic available-actions nil)
(def ^:dynamic plan-fragment-library nil)
(def ^:dynamic verbosity 3)

(def ^:dynamic *printdebug* false) ; false

(defn nyi
  [text]
  (if (> verbosity 1) (println "NYI called with: " text))
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; IR constructors

(defn ir-field-ref
  [names]
  {:type :field-ref,
   :names names})

(defn ir-method-call
  [methodref args]
  {:type :method-fn,
   :method-ref methodref,
   :args args
   })

(defn ir-sequence
  [body]
  {:type :sequence,
   :body body})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Virtual states

(defn snapshot-modeled-state
  "Create a snapshot of the current state"
  []
  (nyi "snapshot-modeled-state"))

(defn reset-modeled-state
  [virtual-state-snapshot]
  (nyi "reset-modeled-state"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; pamela-ir construction

(defn construct-method-ir
  [action subgoals]
  (nyi "construct-method-ir"))

(defn construct-pclass-ir
  [methods]
  (nyi "construct-pclass-ir"))

(defn generate-selected-plan-as-pclass-ir
  "Having selected a plan, produce a representation of it as a Pamela pclass in ir format"
  [action-subgoal-pairs]
  ;; Assemble the actions/subgoals into methods
  (let [methods (seq (map (fn [action subgoals] (construct-method-ir action subgoals) action-subgoal-pairs)))
        planclass (construct-pclass-ir methods)]
    planclass))

(defn actions-whose-posts-match-goal
  [goal goal-constraints]
  (nyi "actions-whose-posts-match-goal"))

(defn monte-carlo-select
  [actions]
  (nyi "monte-carlo-select"))

(defn find-an-action-to-achieve
  ;; Using known actions of the fragment database produce a list of the actions capable of realising the goal.
  ;; The selection is made using Monte-Carlo sampling with considers the other constraints that it may simultaneously meet.
  [goal goal-constraints]
  (let [actions (actions-whose-posts-match-goal goal goal-constraints)]
    (monte-carlo-select actions)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; End-to-end samples


(defn select-preferred-order-of-actions
  [actions goal-constraints]
  (nyi "select-preferred-order-of-actions"))

(defn evaluate-sample-quality
  [action-subgoal-pairs]
  (nyi "evaluate-sample-quality"))

(defn evaluate-prerequisite
  [apre]
  (nyi "evaluate-prerequisite"))

(defn action-prerequisites
  [anact]
  (nyi "evaluate-prerequisite"))

(defn unsatisfied-prerequisites
  "Find the prerequisites of an action that are not already met in the current state."
  [anaction]
  (let [prerequisites (action-prerequisites anaction)]
    (remove nil? (map (fn [apre]
                        (if (= (evaluate-prerequisite apre) true)
                          nil           ; This prerequisit is already true
                          apre))
                      prerequisites))))

(defn generate-plan-sample
  "Given a set of goal state constraints, produce a sample plan."
  [goal-constraints]
  (let [- (if (> verbosity 1) (println "New Sample"))
        ;;  Snapshot the state in order to be able to replay for other samples.
        virtual-state-snapshot (snapshot-modeled-state)
        ;; For each goal constraint, find an action likely to achieve it chosen by Monte-Carlo weighted random selection.
        actions (seq (map (fn [goal] (find-an-action-to-achieve goal goal-constraints)) goal-constraints))
        - (if (> verbosity 1) (println "Top-level-actions: " actions)) ; debugging statement
        ;; Order the actions in order to optimize the progression towards the overall goal state.
        sorted-actions (select-preferred-order-of-actions actions goal-constraints)
        ;; For each action, establish a list of unsatisfied prerequisites and establish them as subgoals.
        subgoals (seq (map (fn [anaction] (unsatisfied-prerequisites anaction)) sorted-actions))
        ;; Reset state to starting state in preparation of the subsequent sample
        action-subgoal-pairs (seq (map (fn [action subgoals] [action subgoals]) sorted-actions subgoals))
        evaluate-sample (evaluate-sample-quality action-subgoal-pairs)
        - (reset-modeled-state virtual-state-snapshot)
        ]
    ;;[action-subgoal-pairs evaluation]
    nil))

(defn value?
  [v]
  (and (sequential? v) (= (first v) :value)))

(defn print-condition-tersely
  [condition]
  (if (= (first condition) :thunk)
    (do
      (print "[:thunk ")
      (pprint (second condition))
      (println (.variable (nth condition 2)) "]"))
    (pprint condition))
  nil)

(defn generate-lookup-from-condition
  "Translate a goal condition into lookups for the inverse influence table."
  [pclass condition]

  (if (> verbosity 2) (println "In generate-lookup-from-condition: pclass=" pclass "condition: "))
  (if (> verbosity 2) (print-condition-tersely condition))

  (if (sequential? condition)               ;atomic conditions = no influence
    (case (first condition)
      :thunk (let [[cond rto] (rest condition)] (generate-lookup-from-condition pclass cond))
      :equal (let [[arg1 arg2] (rest condition)
                   arg1 (if (value? arg1) (second arg1) arg1)
                   arg2 (if (value? arg2) (second arg2) arg2)]
               (cond (or (and
                          (or (rtm/RTobject? arg1) (= (first arg1) :field))
                          (or (keyword? arg2) (= (first arg2) :mode-of)))
                         (and
                          (or (rtm/RTobject? arg2) (= (first arg2) :field))
                          (or (keyword? arg1) (= (first arg1) :mode-of))))
                     (list [condition [:any [:arg-mode]]])

                     (rtm/RTobject? arg1)
                     (list [condition [:object arg1]]) ;+++ surely we want to get both cases

                     (rtm/RTobject? arg2)
                     (list [condition [:object arg2]])

                     (and (= (first arg1) :field))
                     (list [condition [pclass [:field (second arg1)]]]) ;+++ surely we want to get both cases

                     (and (= (first arg2) :field))
                     (list [condition [pclass [:field (second arg2)]]])

                     (and (= (first arg1) :arg-field))
                     (list [condition [pclass [:arg-field (second arg1)]]])

                     (and (= (first arg2) :arg-field))
                     (list [condition [pclass [:arg-field (second arg2)]]])

                     :else nil #_(list [pclass (extract-referents condition)]))) ; NYI+++
      ;; NYI +++ :and (apply concat (map (fn [arg] (compile-influence arg)) (rest condition)))
      :not (list [:not]) ;+++
      nil)
    nil))                                  ;NYI

(defn get-desired-mode
  [goal]
  (cond (= (first goal) :equal)
        (first (remove nil? (map (fn [part] (get-desired-mode part)) (rest goal))))

        (= (first goal) :mode-of)
        (nth goal 2)

        (and (= (first goal) :value) (keyword? (nth goal 1)))
        (nth goal 1)

        :otherwise nil))                ; +++ handle harder cases +++

;;; (desired-mode '[:equal [:field abanana] [:mode-of (Banana) :eaten]])

(defn guaranteed-modes-aux
  [condition]
  (cond (= (first condition) :mode-of)
        (nth condition 2)

        (= (first condition) :equal)
        (remove nil? (map guaranteed-modes-aux (rest condition)))

        (= (first condition) :and)
        (apply concat (map guaranteed-modes-aux (rest condition)))

        ;; +++ handle cases for or and not
        :otherwise nil))

(defn guaranteed-modes
  [anmq]
  (let [pclass (.pclass anmq)]
    #_(println ".methodsig=" (.methodsig anmq) " .postc=" (irx/.postc (.methodsig anmq)))
    (guaranteed-modes-aux (irx/.postc (.methodsig anmq)))))

#_(guaranteed-modes (MethodQuery.
                     'Robot
                     (irx/MethodSignature.
                      'eat
                      '[:and
                        [:equal [:field handholds] [:arg object]]
                        [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]]
                      '[:and
                        [:equal [:arg object] [:mode-of (Foodstate) :eaten]]
                        [:equal [:field handholds] [:mode-of (General) :nothing]]]
                      '(1.0)
                      '(object))))

(defn mode-signature
  [sig]
  (= sig [:any [:arg-mode]]))

;;;  (and (= (first sig) :any) (= (first (second sig)) :arg)))

(defn y-or-n?
  [message]
  (println message "(type y or n) ?")
  (case (let [answer (read) - (println answer)] answer)
    y true
    n false
    (recur message)))

(defn argpart
  [postconds]
  (if (= (first (nth postconds 1)) :arg)
    (nth postconds 1)
    (if (= (first (nth postconds 2)) :arg) (nth postconds 2) nil)))

(defn nonargpart
  [postconds]
  (if (not (= (first (nth postconds 1)) :arg))
    (nth postconds 1)
    (if (not (= (first (nth postconds 2)) :arg)) (nth postconds 2) nil)))

;;; +++ we need to handle all of the cases here especially multiple precondition case+++
(defn match-goal-query-aux
  [goal postconds]
   (if (> verbosity 2) (println "in match-goal-query-aux with (" goal "," postconds ")"))
  (if (= (first goal) (first postconds))
    (case (first goal)
      :equal (let [argcondpart (argpart postconds)
                   -  (if (> verbosity 2) (println "argcondpart=" argcondpart))
                   matchcondpart (nonargpart postconds)
                   - (if (> verbosity 2) (println "matchcondpart=" matchcondpart))
                   matchresult (if (and argcondpart matchcondpart)
                                 (if (= matchcondpart (nth goal 1))
                                   (into {} (list [(second argcondpart) (nth goal 2)]))
                                   (if (= matchcondpart (nth goal 2))
                                     (into {} (list [(second argcondpart) (nth goal 1)]))
                                     nil)))]
               (if (> verbosity 2) (println "match " matchcondpart " with " goal " goal =" matchresult))
               matchresult)
      (do (if (> verbosity 2) (println "match-goal-query-aux unhandled case: goal=" goal " posts=" postconds))
          nil))
    (do (if (> verbosity 2) (println "match-goal-query-aux unhandled case: goal=" goal " posts=" postconds))
        nil)))

(defn match-goal-query?
  [goal query]
  (let [postconds (irx/.postc (.methodsig query))]
    (match-goal-query-aux goal postconds)
    #_(y-or-n? (str "match?"
                  (with-out-str (print goal))
                  " with "
                  (with-out-str (print postconds))))))

(defn verify-candidate
  [acand]
  (let [[goal signature cmethods rootobj rtobj] acand
        rtotype (get rtobj :type)
        - (if (> verbosity 2) (println "goal=" goal " sign=" signature " methods=" cmethods))
        methods (rtm/get-controllable-methods) ; Cache this, no need to recompute all the time.+++
        ;;- (do (println "Controllable-methods:") (pprint methods))
        ;; Step 1: Filter out methods that dont match either by pclass or by name
        matchingmethods (remove nil? (map (fn [[pclass pmethod rtobj]]
                                            (if (and (= pclass rtotype)
                                                     (or (= (first signature) :any)
                                                         ;;(= (first signature) (irx/.mname pmethod))
                                                         (= (first signature) (rtm/get-root-class-name)))
                                                     (some #{(irx/.mname pmethod)} cmethods))
                                              (do
                                                (if (> verbosity 2) (println "pc= " pclass " pm=" (.mname pmethod)))
                                                (MethodQuery. pclass pmethod rootobj rtobj))
                                              nil))
                                          methods))
        ;; - (do (println "matchingmethods1:") (pprint matchingmethods))
        desired-mode (if (mode-signature signature) (get-desired-mode goal) nil)
        ;; - (if desired-mode (println "matchingmethods1b - desired-mode=" desired-mode))

        ;; Step 2: for mode comparisons filter out cases that don't guarantee the desired mode
        matchingmethods (if (not (nil? desired-mode))
                          (remove nil? (map (fn [query]
                                              ;; (println "query = " query)
                                              ;; (println "*******")
                                              (if (some  #{desired-mode} (guaranteed-modes query))
                                                query
                                                nil))
                                            matchingmethods))
                          ;; Otherwise handle case where an argument reference matches our goal
                          ;; influence is a weak runfilter, some matches will not help. It is here where we
                          ;; weed out the unhelpful matches.
                          (remove nil? (map (fn [query]
                                              #_(println "query=" query)
                                              #_(println ".methodsig=" (.methodsig query)
                                                       " .postc=" (irx/.postc (.methodsig query)))
                                              (if (match-goal-query? goal query)
                                                query
                                                nil))
                                            matchingmethods)))
        ;; - (do (println "matchingmethods2:") (pprint matchingmethods))
        ]
    matchingmethods))

;;; Non learning version +++ replace with learning version when fixed!
(defn select-candidate
  [cands]
  (if (not (empty? cands)) (list (rand-nth cands)) nil))

(defn get-references-from-value
  [val]
  (cond (keyword? val) nil
        (rtm/RTobject? val) [[:foo val]])) ; unfinished

(defn get-ir-references-from-expression
  "Generate the ir for the expression and the mapping from the argument name to the expression and its IR."
  ;; +++ currently only produces the IR and not the mapping.
  [expn]
  ;; (println "In get-references-from-expression, expn=" expn)
  (cond (= (first expn) :field) [(ir-field-ref [(second expn)])]             ;+++ here is wher IR leaks into conditions +++
        (= (first expn) :value) (get-references-from-value (second expn))
        (= (first expn) :arg) [[:arg-ref (first expn) (second expn)]] ; +++ placeholder
        (= (first expn) :mode-of) nil
        :otherwise nil))

(defn get-references-from-expression
  "Generate the ir for the expression and the mapping from the argument name to the expression and its IR."
  ;; +++ currently only produces the IR and not the mapping.
  [expn]
  ;; (println "In get-references-from-expression, expn=" expn)
  (cond (= (first expn) :field) [expn] ;[(ir-field-ref [(second expn)])]
        (= (first expn) :value) (get-references-from-value (second expn))
        (= (first expn) :arg) [[:arg-ref (first expn) (second expn)]] ; +++ placeholder
        (= (first expn) :mode-of) nil
        :otherwise nil))

(defn get-references-from-condition
  [condition]
  (let [result (cond
                 (= (first condition) :thunk)
                 (into [] (map (fn [ref] [:thunk ref (nth condition 2)])
                               (get-references-from-condition (second condition))))

                 (= (first condition) :equal)
                 (into [] (apply concat (map (fn [expn] (get-references-from-expression expn)) (rest condition))))

                 :otherwise (do (irx/error "Unhandled case in get-references-from-condition: " condition) nil))]
    (if (> verbosity 2) (println "in get-references-from-condition, condition=" condition "=" result))
    result))

;;; Args are evaluated from the standpoint of the root
(defn make-args-map-and-args
  [formals actuals wrtobject]
  (if (not (= (count formals) (count actuals)))
    (irx/error  "Wrong Number of Arguments in: make-args-map-and-args formals=" formals " actuals=" actuals))
  (let [- (if (> verbosity 2) (println "*** make-args-map-and-args: " actuals "wrtobject=" wrtobject))
        argsmap (into {} (map (fn [f a] [f a]) formals actuals))]
    (if (> verbosity 2) (println "argsmap=" argsmap))
    [actuals argsmap]))

(defn find-query-in-goal
  [querypart goal]
  (case (first goal)
    :thunk (find-query-in-goal querypart (second goal))
    :equal (cond (= querypart (nth goal 1)) (nth goal 2)
                 (= querypart (nth goal 2)) (nth goal 1)
                 :otherwise nil)
    [:unhandled-case-in-find-query-in-goal goal]))

(defn get-goal-reference
  [query goal]
  (find-query-in-goal (second query) goal))

(defn describe-goal
  [agoal]
  ;; (println "In describe-goal with agoal=" agoal)
  (if (= (first agoal) :thunk)
    (pprint [:thunk (second agoal) (.variable (nth agoal 2))])
    (pprint agoal)))

(defn describe-goals
  [goals]
  (if (> verbosity 2) (println))
  (if (> verbosity 2) (println "***Current outstanding goals:"))
  (if (> verbosity 2)
    (doseq [agoal goals]
      (describe-goal agoal))))

;;; A call comes 'from' the root 'to' the controllable.
(defn compile-arglist
  "Returns [argsmap actuals]."
  [action goal query wrtobject]
  (if (> verbosity 2) (println "compile-arglist action=" (.mname (.methodsig action)) " query=" query " and goal:"))
  (if (> verbosity 2) (describe-goal goal))
  (let [pcls (.pclass action)
        msig (.methodsig action)
        argnames (.arglist msig)
        mname (.mname msig)
        -     (if (> verbosity 2) (println "class/method/argnames=" pcls mname argnames))
        returnvals
        (cond
          ;; Handle arglist by query type
          (= query [:any [:arg-mode]])
          ;; Here we are looking to provide the object being affected
          (make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal)) wrtobject)

          :otherwise
          (make-args-map-and-args argnames [(irx/compile-reference (get-goal-reference query goal))] wrtobject) ;+++ why only one?

          #_(let [amap (match-goal-query? goal query)]
              (make-args-map-and-args argnames (map (fn [arg]
                                                      (irx/compile-reference (get amap arg)))
                                                    argnames)))
          #_(make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal))))]
    (if (> verbosity 2) (println "compile-arglist returns:" returnvals))
    returnvals))

(defn compile-controllable-object
  [action goal query]
  (let [objs (rtm/get-root-objects-of-type (.pclass action))
        object (first objs)]  ;+++ what about if there are multiple such objects? +++
    object))

(defn replace-args-with-bindings
  [condit argmap]
  (let [replaced (if (not (vector? condit))
                   condit
                   (case (first condit)
                     :call (into [(nth condit 0) (nth condit 1) (nth condit 2)]
                                 (map (fn [subexp]
                                        (replace-args-with-bindings subexp argmap))
                                      (rest (rest (rest condit)))))
                     :arg (get argmap (second condit))
                     :arg-field [:arg-field
                                 (get argmap (nth condit 1))
                                 (nth condit 2)]
                     (:and :or :not :equal) (into [(first condit)]
                                                  (map (fn [subexp]
                                                         (replace-args-with-bindings subexp argmap))
                                                       (rest condit)))
                     condit))]
    (if (> verbosity 2) (println "replace-args-with-bindings - condit=" condit " argmap=" argmap " replaced=" replaced))
    replaced))

;;; Format of an action is: [pclass (method-name [preconditions][postconditions] (probability) (list-of-args))]
(defn compile-call
  "Given a call, construct the IR for the call and return also the prerequisites
   and the bindings, as a vector [ir-call vector-of-prerequisites vector-of-bindings]."
  [action goal query root-objects wrtobject]
  #_(println "action=" action " query=" query " and goal:")
  (if (> verbosity 2) (describe-goal goal))
  (let [[args argmap] (compile-arglist action goal (second query) wrtobject)  ;+++ kludge "second" +++ was (first root-objects)
        object (compile-controllable-object action goal (second query))] ;+++ kludge "second"
    [(ir-method-call (ir-field-ref [object (irx/.mname (.methodsig action))]) args)
     (replace-args-with-bindings (irx/.prec (.methodsig action)) argmap)]))

(defn compile-calls
  [actions goal queries root-objects rtos]
  (let [compiled-calls
        (remove nil? (map (fn [query action rto]
                            (if action
                              (compile-call action goal query root-objects rto)
                              (do (irx/error "Missing action in compile-call") nil)))
                          queries actions rtos))]
    compiled-calls))

;; (defn sanitize-calls
;;   [calls]
;;   (map (fn [acall]
;;          (map (fn [term] ...)
;;          (acall)
;;        calls)) ..))

(defn scompile-call-sequence
  [calls]
  ;; (println "**** In scompile-call-sequence calls:")
  (pprint calls)
  (let [;; scalls (sanitize-calls calls)
        sequence (ir-sequence (into [] calls))
        - (if (> verbosity 2) (do (println "sequence:") (pprint sequence)))
        code-source-fragment
        (with-out-str
            (println (pup/unparse-fn sequence)))]
    code-source-fragment))

;;; simplify condition always returns a list representing a conjunction.
(defn simplify-condition [condit wrtobject])

;;; simplify-negate always returns an individual expression
(defn simplify-negate
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit wrtobject]
  ;; (println "in simplify-negate with: condit=" condit)
  (if (not (or (seq? condit) (vector? condit)))
    condit
    (case (first condit)
      ;; NOT NOT cancels, return the simplified subexpression
      :not (let [exps (simplify-condition (second condit) wrtobject)]
             ;; Handle case where expression of not simplified to a conjunction.
             (case (count exps)
               0 true
               1 (first exps)
               (into [:and] exps)))
      ;; OR ~(Happy OR Sad) = ~Happy AND ~Sad
      :or (into [:and] (map (fn [sc] (simplify-negate sc wrtobject)) (rest condit)))
      ;; AND - ~(Happy AND Sad) = ~Happy OR ~Sad
      :and (into [:or] (map (fn [sc] (simplify-negate sc wrtobject)) (rest condit)))
      [:not condit])))

;;; [:and [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]]

(defn conjunctive-list
  [condit]
  (case (first condit)
    :and (rest condit)
    :or [condit]
    :not [condit]
    [condit]))

;; In un-lvar-expression with exprn= [:field p3]
;; In un-lvar-expression with exprn= [:mode-of (TargetStates) :attacked]
;; In un-lvar-expression with exprn= [:arg-field [:field atarget] location]

(defn un-lvar-expression
  [exprn wrtobject]
  (let [evaluated (rtm/evaluate-reference wrtobject exprn nil nil nil nil)
        bound-value (if (and (rtm/is-lvar? evaluated) (rtm/is-bound-lvar? evaluated)) (rtm/deref-lvar evaluated) false)
        - (if (> verbosity 2) (println "In un-lvar-expression with exprn=" exprn "evaluates to " evaluated))
        - (if (> verbosity 2) (if bound-value (println "****" (.name evaluated) "=" bound-value)))
        result (if (sequential? exprn)
                 (case (first exprn)
                   :field (if bound-value [:field [:value bound-value]] exprn)
                   :mode-of exprn                    ; Perhaps allow the class and the value to be lvared?+++
                   :arg-field exprn
                   exprn)
                 exprn)]
    (if (not (= exprn result)) (if (> verbosity 2) (println "LVAR binding applied: was: " exprn "now:" result)))
    result))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; simplify-condition
;;;
;;; Converts comdition to conjunctive normal form after simplifying the parts.
;;;
;;; Return s a conjunctive list

(defn simplify-condition
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit wrtobject]
  ;; (println "In simplify condition with: " condit)
  (if (not (or (list? condit) (vector? condit)))
    (list condit)
    (let [result (case (first condit)
                   :thunk (list
                           (into [:thunk]
                                 (into (into [] (simplify-condition (nth condit 1) (nth condit 2))) [(nth condit 2)])))

                   :equal (list
                           [:equal
                            (un-lvar-expression (nth condit 1) wrtobject)
                            (un-lvar-expression (nth condit 2) wrtobject)])
                   ;; NOT negate the simplified subexpression
                   :not (conjunctive-list (simplify-negate (second condit) wrtobject))
                   ;; AND return the simplified parts as a list.
                   :and (apply concat (map (fn [sc] (simplify-condition sc wrtobject)) (rest condit)))
                   ;; OR - Happy OR Sad = ~(~Happy AND ~Sad)
                   :or (conjunctive-list (simplify-negate (into [:and]
                                                                (map (fn [sc]
                                                                       (simplify-negate sc wrtobject))
                                                                     (rest condit)))
                                                          wrtobject))
                   :field (conjunctive-list [:value (un-lvar-expression condit wrtobject)])
                   [condit])
          simpres (remove (fn [x] (= x true)) result)]
      ;; (println "simplified=" result "simpres=" simpres)
      (if (> verbosity 2) (do
                            (println "In simplify-condition: simpres: ")
                            (print-condition-tersely simpres)))
      simpres)))

(defn simplify-cond-top-level
  [condit wrtobject]
  (if (> verbosity 2) (println "In Simplify with wrtobject=" (.variable wrtobject)))
  (let [simplified (simplify-condition condit wrtobject)
        terms (count simplified)]

    ;; (print "*** SIMPLIFY ")
    ;; (describe-goal condit)
    ;; (print " = ")
    ;; (describe-goal simplified)

    (if (> terms 1)
      simplified ;(list (into [:and] simplified))
      simplified)))

;;; (simplify-condition '[:and [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]] nil)
;;; (simplify-condition '[:or [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]] nil)

#_(defn substitute-bindings
  [condit bindings]
  ;; This call is no longer needed since we do substitution earlier.
  ;(println "in substitute-bindings with: " condit)
    condit)

;;; This is the non-learning version to begin with - learning version still needs debugging
(defn mcselect
  [choices]
  (rand-nth choices))

;;; Always return true or false, if true, may bind lvars
(defn select-and-bind2
  [arg1 arg2 matches]
  (let [num-matches (count matches)]
    (if (> verbosity 2) (println "In select-and-bind2: num-matches=" num-matches "here: " matches))
    (if (empty? matches)
      false                           ; Nothing found, no variables bound : FAIL
      (let [selection (mcselect matches)
            {ptype :ptype, subj :subject, obj :object} selection]
        (if (rtm/is-lvar? arg1)
          (do
            (if (> verbosity 2) (println "*** Binding LVAR"))
            (rtm/bind-lvar arg1 subj)
            (if (> verbosity 2) (rtm/describe-lvar arg1))))
        (if (rtm/is-lvar? arg2)
          (do
            (if (> verbosity 2) (println "*** Binding LVAR"))
            (rtm/bind-lvar arg2 obj)
            (if (> verbosity 2) (rtm/describe-lvar arg2))))
        true))))

(defn internal-condition-call
  [plant name args]
  (case plant
    'dmcp
    (case name
      'find-binary-proposition
      (let [[pname arg1 arg2] args ; Presently pname must be supplied allow lvar for pname later ? +++
            arg1-unbound-lvar (and (rtm/is-lvar? arg1) (not (rtm/is-bound-lvar? arg1)))
            arg2-unbound-lvar (and (rtm/is-lvar? arg2) (not (rtm/is-bound-lvar? arg2)))
            ;; Dereference bound LVARS
            arg1 (if (and (rtm/is-lvar? arg1) (rtm/is-bound-lvar? arg1)) (rtm/deref-lvar arg1) arg1)
            arg2 (if (and (rtm/is-lvar? arg2) (rtm/is-bound-lvar? arg2)) (rtm/deref-lvar arg2) arg2)]
        (if (> verbosity 2) (println "in internal-condition-call with pname=" pname
                                     " arg1=" (if arg1-unbound-lvar :unbound arg1)
                                     " arg2=" (if arg2-unbound-lvar :unbound arg2)))
        (cond ;; There are 4 cases, one bound, the other bound, both bound, neither bound
          (not (or arg1-unbound-lvar arg2-unbound-lvar)) ; both bound
          (select-and-bind2 arg1 arg2 (bs/find-binary-propositions-matching #{arg1} nil #{pname} nil #{arg2} nil))

          (and arg1-unbound-lvar (not arg2-unbound-lvar)) ; arg2 bound
          (select-and-bind2 arg1 arg2 (bs/find-binary-propositions-matching nil nil #{pname} nil #{arg2} nil))

          (and (not arg1-unbound-lvar) arg2-unbound-lvar) ; arg1 bound
          (select-and-bind2 arg1 arg2 (bs/find-binary-propositions-matching #{arg1} nil #{pname} nil nil nil))

          (and arg1-unbound-lvar arg2-unbound-lvar) ; This is a strange request, but not illegal
          (select-and-bind2 arg1 arg2 (bs/find-binary-propositions-matching nil nil #{pname} nil nil nil))

          :otherwise (irx/error "internal-condition-call: can't get here, arg1=" arg1 " arg2=" arg2)))

      (irx/error "Internal-condition-call: Unknown function: " name))

    (irx/error "Internal-condition-call: Can't get here, plant =" plant)))

;;; Why not just push all of this into rtm/evaluate?

(defn condition-satisfied?
  [condit wrtobject]
  (if (not (sequential? condit))
    condit ; (irx/error "In condition-satisfied? condit = " condit)
    (case (first condit)
      :thunk
      (let [[acondit wrtobj] (rest condit)]
        (condition-satisfied? acondit wrtobj))
      ;; NOT negate the recursive result
      :not (not (condition-satisfied? (second condit) wrtobject))
      ;; AND - check that all subextressions are satisfied
      :and (every? (fn [condit] (condition-satisfied? condit wrtobject)) (rest condit))
      ;; OR - true if at least one subexpression is satisfied
      :or (some (fn [condit] (condition-satisfied? condit wrtobject)) (rest condit))
      ;; EQUAL -
      :equal ;(y-or-n? (str "(condition-satisfied? " (with-out-str (print condit)) ")"))
      (do
        (if (> verbosity 2) (println "In condition-satisfied? with (= "
                                     (with-out-str (print (nth condit 1)))
                                     (with-out-str (print (nth condit 2)))
                                     ")"))
        (let [first-expn (rtm/evaluate  wrtobject (nth condit 1) nil nil nil nil)
              first-expn (if (rtm/is-lvar? first-expn) (rtm/deref-lvar first-expn) first-expn)
              second-expn (rtm/evaluate wrtobject (nth condit 2) nil nil nil nil)
              second-expn (if (rtm/is-lvar? second-expn) (rtm/deref-lvar second-expn) second-expn)]
          (if (> verbosity 2) (println "(= "
                                       (with-out-str (print (nth condit 1))) "=" first-expn
                                       (with-out-str (print (nth condit 2))) "=" second-expn
                                       ")"))
          (= first-expn second-expn)))
      :call
      (let [plant (nth condit 1)
            names (nth condit 2)
            args (doall (map (fn [arg]
                               (rtm/evaluate wrtobject arg nil nil nil nil))
                             (rest (rest (rest condit)))))]
        (cond (= plant 'dmcp) ;+++ dmcp handled specially
              (internal-condition-call plant (first names) args)

              :otherwise (do (irx/break "CALL: plant=" plant " names=" names " args=" args) true)))

      (irx/error "(condition-satisfied? " condit ")"))))

(defn plan-generate
  [root-objects controllable-objects pclass list-of-goals max-depth]
  (loop [goals list-of-goals        ; List of things to accomplish
         ;; wrtobject (second (first root-objects))
         complete-plan []           ; List of actions collected so far
         depth 0]
    (if (>= depth max-depth)
      (if (> verbosity 2) (do (println "DMCP: Aborting sample because maximum depth of " max-depth " has been reached.")
                              (println "************************************************************************")
                              nil))
      (let [goals (apply concat (map (fn [agoal] (simplify-cond-top-level agoal (second (first root-objects)))) goals))
            - (if (> verbosity 2) (describe-goals goals))
            this-goal (first goals)        ; We will solve this goal first
            rootobject (second (first root-objects))
            - (if (> verbosity 2) (println "Solving for:"))
            - (if (> verbosity 2) (describe-goal this-goal))
            outstanding-goals (rest goals)] ; Afterwards we will solve the rest

        (rtm/start-plan-bind-set)

        (if (condition-satisfied? this-goal rootobject)
          (if (empty? outstanding-goals)
            (do (if (> verbosity 2) (println "***Solution found:"))
                (pprint complete-plan)
                (if (> verbosity 2) (println "************************************************************************"))
                complete-plan)                 ; The last outstanding goal was satisfied, return the completed plan SUCCESS
            (recur outstanding-goals complete-plan depth)) ; Continue until we reach an unsatisfied goal
          ;; Now we have a goal that requires effort to solve.

          (do
            (rtm/stop-plan-bind-set)

            (let [queries (generate-lookup-from-condition pclass this-goal)
                  - (if (> verbosity 2) (println "Root query=" queries))
                  iitab (rtm/inverted-influence-table)
                  - (if (> verbosity 2) (println "iitab=" iitab))
                        candidates (apply concat (map (fn [[agoal aquery]]
                                                        (map (fn [[coid ctrlobj]]
                                                               [agoal aquery (get iitab aquery) rootobject ctrlobj])
                                                             controllable-objects))
                                                      queries))    ;+++ need to handle nested queries+++
                        ;; - (do (println "candidates=") (pprint candidates))
                        candidates (apply concat (map (fn [cand] (verify-candidate cand)) candidates))
                        ;; - (do (println "good candidates=") (pprint candidates))
                        ;; Now select a method if no match, generate a gap filler
                        selected (select-candidate candidates)] ;+++ generate a gap filler if necessary +++
                  (if selected                                ; If we have found an action to try prepare it, otherwise we fail
                    (let [rtos (map (fn [anmq] (.rto anmq)) selected)
                          actions (compile-calls selected this-goal queries root-objects rtos) ;
                          ;; - (println "actions=" actions)
                          subgoals (apply concat (map (fn [[call prec] rto]
                                                        (if (not (rtm/RTobject? rto)) (irx/error "not an RTobject: " rto))
                                                        (map (fn [conj] [:thunk conj rto])
                                                             (simplify-cond-top-level prec rto)))
                                                      actions rtos))
                          ;;subgoals (apply concat (map (fn [[call prec]] (simplify-cond-top-level prec nil)) actions))
                          outstanding-goals  (remove nil? (concat subgoals outstanding-goals))]

                      ;;(println "selected=" selected)
                      ;;(println "actions=" actions)
                      ;;(println "subgoals=" subgoals)
                      (let [plan-part (concat actions complete-plan)]
                        (if (> verbosity 2) (println "ACTION-TAKEN: " actions))
                        (if (empty? outstanding-goals)
                          plan-part             ; Current action has no prerequisited (rare) and there are none outstanding SUCCESS
                          (recur outstanding-goals plan-part (+ 1 depth)))))
                    (do
                      (if (> verbosity 2) (println "DMCP: sample failed"))
                      (if (> verbosity 2) (println "************************************************************************"))
                      nil)))))))))                     ; We failed to find a solution, return nil

(defn plan
  [root-objects controllable-objects pclass list-of-goals & {:keys [max-depth] :or {max-depth 10}}]
  (let [completed-plan (plan-generate root-objects controllable-objects pclass list-of-goals max-depth)]
    completed-plan))


;;; For each action, create a binding list for named argument to a value, then use that
;;; binding list to replace each occurrence of that argument in
;;; the prerequisites.  This allows the prerequisites to stand alone from their call.
;;;
;;; Round 2 prerequisites
;;; ([:and
;;;   [:equal [:field handholds] [:arg object]]
;;;   [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])

(defn solveit
  "Generate a plan for the goals specified in the model."
  [& {:keys [samples max-depth rawp] :or {samples 10 max-depth 10 rawp false}}]
  (if (> verbosity 0) (println "DMCP: solving with " samples "samples, max-depth=" max-depth))
  (loop [solutions ()
         sampled 0]
    (if (> verbosity 1) (println "DMCP: " (count solutions) "found so far out of " sampled " samples."))
    (if (>= sampled samples)
      (if (not (empty? solutions))                         ; We have done enough, return what we have
        (do
          (if (> verbosity 0) (println "DMCP: " (count solutions) "found out of " sampled " samples."))
          (doall solutions))
        nil)      ; And it turns out that we didn't find any solutions. nil result signifies failure
      (let [root-objects (rtm/get-root-objects)
            ;; - (println "root-objects=" root-objects)
            controllable-objects (rtm/get-controllable-objects)
            ;; - (println "controllable-objects=" controllable-objects)
            [pclass goal-conds] (rtm/goal-post-conditions)
            - (if (> verbosity 2) (do (println "Root PCLASS=" pclass "GOAL:")(pprint goal-conds)))
            actions (plan root-objects controllable-objects pclass
                          (map (fn [agoal]
                                 [:thunk agoal (second (first root-objects))]
                                 #_agoal)
                               (simplify-cond-top-level goal-conds (second (first root-objects))))
                          :max-depth max-depth)
            ;; +++ Now put the call into the solution
            compiled-calls (if actions (if rawp
                                         actions
                                         (scompile-call-sequence (seq (map first actions)))))]
        ;;(pprint actions)
        (recur (if compiled-calls (cons compiled-calls solutions) solutions) (+ 1 sampled))))))

;;; (solveit)


;;; Fin
