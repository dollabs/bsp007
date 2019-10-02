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

(defrecord MethodQuery [pclass methodsig])

(def ^:dynamic available-actions nil)
(def ^:dynamic plan-fragment-library nil)
(def ^:dynamic verbosity 0)

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
                        (if (= (evaluate-prerequisite apre) :true)
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

(defn generate-lookup-from-condition
  "Translate a goal condition into lookups for the inverse influence table."
  [pclass condition]
  (if (vector? condition)               ;atomic conditions = no influence
    (case (first condition)
      :equal (cond (or (and (= (first (nth condition 1)) :field)
                            (= (first (nth condition 2)) :mode-of))
                       (and (= (first (nth condition 2)) :field)
                            (= (first (nth condition 1)) :mode-of)))
                   (list [condition [:any [:arg-mode]]])
                   (and (= (first (nth condition 1)) :field))
                   (list [condition [pclass [:field (second (nth condition 1))]]]) ;+++ surely we want to get both cases
                   (and (= (first (nth condition 2)) :field))
                   (list [condition [pclass [:field (second (nth condition 2))]]])
                   (and (= (first (nth condition 1)) :arg-field))
                   (list [condition [pclass [:arg-field (second (nth condition 1))]]])
                   (and (= (first (nth condition 2)) :arg-field))
                   (list [condition [pclass [:arg-field (second (nth condition 2))]]])
                   :else nil #_(list [pclass (extract-referents condition)])) ; NYI+++
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
    (println ".methodsig=" (.methodsig anmq) " .postc=" (irx/.postc (.methodsig anmq)))
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
    (if (not (= (first (nth postconds 2)) :arg) (nth postconds 2)) nil)))

;;; +++ we need to handle all of the cases here especially multipkle precondition case+++
(defn match-goal-query-aux
  [goal postconds]
  (println "in match-goal-query-aux with (" goal "," postconds ")")
  (if (= (first goal) (first postconds))
    (case (first goal)
      :equal (let [argcondpart (argpart postconds)
                   - (println "argcondpart=" argcondpart)
                   matchcondpart (nonargpart postconds)
                   - (println "matchcondpart=" matchcondpart)
                   matchresult (if (and argcondpart matchcondpart)
                                 (if (= matchcondpart (nth goal 1))
                                   (into {} (list [(second argcondpart) (nth goal 2)]))
                                   (if (= matchcondpart (nth goal 2))
                                     (into {} (list [(second argcondpart) (nth goal 1)]))
                                     nil)))]
               (println "match " matchcondpart " with " goal " goal =" matchresult)
               matchresult)
      (do (println "match-goal-query-aux unhandled case: goal=" goal " posts=" postconds) nil))
    (do (println "match-goal-query-aux unhandled case: goal=" goal " posts=" postconds) nil)))

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
  (let [[goal signature cmethods] acand
        - (println "goal=" goal " sign=" signature " methods=" cmethods)
        methods (rtm/get-controllable-methods) ; Cache this, no need to recompute all the time.+++
        ;;- (do (println "Controllable-methods:") (pprint methods))
        ;; Step 1: Filter out methods that dont match either by pclass or by name
        matchingmethods (remove nil? (map (fn [[pclass pmethod rtobj]]
                                            (println "pc= " pclass " pm=" pmethod)
                                            (if (and (or (= (first signature) :any)
                                                         ;;(= (first signature) (irx/.mname pmethod))
                                                         (= (first signature) (rtm/get-root-class-name)))
                                                     (some #{(irx/.mname pmethod)} cmethods))
                                              (MethodQuery. pclass pmethod)
                                              nil))
                                          methods))
        - (do (println "matchingmethods1:") (pprint matchingmethods))
        desired-mode (if (mode-signature signature) (get-desired-mode goal) nil)
        - (do (println "matchingmethods1b:") (pprint desired-mode))

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
                          ;; influence is a weak filter, some matches will not help. It is here where we
                          ;; weed out the unhelpful matches.
                          (remove nil? (map (fn [query]
                                              (println "query=" query)
                                              (println ".methodsig=" (.methodsig query)
                                                       " .postc=" (irx/.postc (.methodsig query)))
                                              (if (match-goal-query? goal query)
                                                query
                                                nil))
                                            matchingmethods)))
        - (do (println "matchingmethods2:") (pprint matchingmethods))
        ]
    matchingmethods))

(defn select-candidate
  [cands]
  ;; +++ move  montecarlo calculation and selection into here +++
  (list (first cands)))

(defn get-references-from-expression
  "Generate the ir for the expression and the mapping from the argument name to the expression and its IR."
  ;; +++ currently only produces the IR and not the mapping.
  [expn]
  ;; (println "In get-references-from-expression, expn=" expn)
  (cond (= (first expn) :field) [(ir-field-ref [(second expn)])]
        (= (first expn) :arg) [[:arg-ref (first expn) (second expn)]] ; +++ placeholder
        (= (first expn) :mode-of) nil
        :otherwise nil))

(defn get-references-from-condition
  [condition]
  ;; (println "in get-references-from-condition, condition=" condition)
  (cond (= (first condition) :equal)
        (into [] (apply concat (map (fn [expn] (get-references-from-expression expn)) (rest condition))))

        :otherwise nil))

(defn make-args-map-and-args
  [formals actuals]
  (let [argsmap (into {} (map (fn [f a] [f a]) formals actuals))]
    (println "argsmap=" argsmap)
    [actuals argsmap]))

(defn find-query-in-goal
  [querypart goal]
  (case (first goal)
    :equal (cond (= querypart (nth goal 1)) (nth goal 2)
                 (= querypart (nth goal 2)) (nth goal 1)
                 :otherwise nil)))

(defn get-goal-reference
  [query goal]
  (find-query-in-goal (second query) goal))

(defn compile-arglist
  "Returns [argsmap actuals]."
  [action goal query]
  (println "compile-arglist action=" action " goal=" goal " query=" query)
  (let [pcls (.pclass action)
        msig (.methodsig action)
        argnames (.arglist msig)
        mname (.mname msig)]
    ;; (println "class/method/argnames=" pcls mname argnames)
    (cond
      ;; Handle arglist by query type
      (= query [:any [:arg-mode]])
      ;; Here we are looking to provide the object being affected
      (make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal)))

      :otherwise (make-args-map-and-args argnames [(irx/compile-reference (get-goal-reference query goal))]) ;+++ why only one?

      #_(let [amap (match-goal-query? goal query)]
                   (make-args-map-and-args argnames (map (fn [arg]
                                                           (irx/compile-reference (get amap arg)))
                                                         argnames)))
      #_(make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal))))))

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
                     :arg (get argmap (second condit))
                     :arg-field [:arg-field
                                 (get argmap (nth condit 1))
                                 (nth condit 2)]
                     (:and :or :not :equal) (into [(first condit)]
                                                  (map (fn [subexp]
                                                         (replace-args-with-bindings subexp argmap))
                                                       (rest condit)))
                     condit))]
    (println "replace-args-with-bindings - condit=" condit " argmap=" argmap " replaced=" replaced)
    replaced))

;;; Format of an action is: [pclass (method-name [preconditions][postconditions] (probability) (list-of-args))]
(defn compile-call
  "Given a call, construct the IR for the call and return also the prerequisites
   and the bindings, as a vector [ir-call vector-of-prerequisites vector-of-bindings]."
  [action goal query]
  ;; (println "action=" action " goal=" goal " query=" query)
  (let [[args argmap] (compile-arglist action goal (second query))  ;+++ kludge "second" +++
        object (compile-controllable-object action goal (second query))] ;+++ kludge "second" +++
    [(ir-method-call (ir-field-ref [object (irx/.mname (.methodsig action))]) args)
     (replace-args-with-bindings (irx/.prec (.methodsig action)) argmap)]))

(defn compile-calls
  [actions goal queries]
  (let [compiled-calls
        (remove nil? (map (fn [query action]
                            (if action
                              (compile-call action goal query)
                              (do (println "Missing action in compile-call") nil)))
                          queries actions))]
    compiled-calls))

(defn scompile-call-sequence
  [calls]
  (let [sequence (ir-sequence (into [] calls))
        - (do (println "sequence:") (pprint sequence))
        code-source-fragment
        (with-out-str
            (println (pup/unparse-fn sequence)))]
    code-source-fragment))

;;; simplify condition always returns a list representing a conjunction.
(defn simplify-condition [condit])

;;; simplify-negate always returns an individual expression
(defn simplify-negate
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit]
  ;; (println "in simplify-negate with: condit=" condit)
  (if (not (or (seq? condit) (vector? condit)))
    condit
    (case (first condit)
      ;; NOT nots cancel, return the simplified subexpression
      :not (let [exps (simplify-condition (second condit))]
             ;; Handle case where expression of not simplifies to a conjunction.
             (case (count exps)
               0 :true
               1 (first exps)
               (into [:and] exps)))
      ;; OR ~(Happy OR Sad) = ~Happy AND ~Sad
      :or (into [:and] (map simplify-negate (rest condit)))
      ;; AND - ~(Happy AND Sad) = ~(~Happy OR ~Sad)
      :and (simplify-negate (into [:or] (map simplify-negate (rest condit))))
      [:not condit])))

;;; [:and [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]]

(defn conjunctive-list
  [condit]
  (case (first condit)
    :and (rest condit)
    :or [condit]
    :not [condit]
    [condit]))

(defn simplify-condition
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit]
  (case (first condit)
    ;; NOT negate the simplified subexpression
    :not (conjunctive-list (simplify-negate (second condit)))
    ;; AND return the simplified parts as a list.
    :and (apply concat (map simplify-condition (rest condit)))
    ;; OR - Happy OR Sad = ~(~Happy AND ~Sad)
    :or (conjunctive-list (simplify-negate (into [:and] (map simplify-negate (rest condit)))))
    (list condit)))

;;; (simplify-condition '[:and [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])
;;; (simplify-condition '[:or [:equal [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])

#_(defn substitute-bindings
  [condit bindings]
  ;; This call is no longer needed since we do substitution earlier.
  ;(println "in substitute-bindings with: " condit)
  condit)

(defn condition-satisfied?
  [condit] ; This should guarantee a null plan
  (case (first condit)
    ;; NOT negate the recursive result
    :not (not (condition-satisfied? (second condit)))
    ;; AND - check that all subextressions are satisfied
    :and (every? condition-satisfied? (rest condit))
    ;; OR - true if at least one subexpression is satisfied
    :or (some condition-satisfied? (rest condit))
    ;; EQUAL -
    :equal (y-or-n? (str "(condition-satisfied? " (with-out-str (print condit)) ")"))
    ;; (let [first-expn (evaluate (second condit))
    ;;       second-expn (evaluate (third condit))]
    ;;   (print "(= "
    ;;          (with-out-str (print (second condit))) "=" first-expn
    ;;          (with-out-str (print (third condit))) "=" second-expn
    ;;          ")")
    ;;   (= first expn second expn))
    (do (println "(condition-satisfied? " condit ")") true)))

(defn plan
  [root-objects controllable-objects pclass list-of-goals]
  (loop [goals list-of-goals        ; List of things to accomplish
         complete-plan []]          ; List of actions collected so far
    (println "Current outstanding goals=" goals)
    (let [this-goal (first goals)        ; We will solve this goal first
          - (println "Solving for =" this-goal)
          outstanding-goals (rest goals)] ; Afterwards we will solve the rest
      (if (condition-satisfied? this-goal)
        (if (empty? outstanding-goals)
          complete-plan
          (recur outstanding-goals complete-plan))
        (let [queries (generate-lookup-from-condition pclass this-goal)
              - (do (println "Root query=") (pprint queries))
              iitab (rtm/inverted-influence-table)
              - (do (println "iitab=") (pprint iitab))
              candidates (map (fn [[agoal aquery]] [agoal aquery (get iitab aquery)])
                              queries)    ;+++ need to handle nested queries+++
              - (do (println "candidates=") (pprint candidates))
              candidates (apply concat (map (fn [cand] (verify-candidate cand)) candidates))
              - (do (println "good candidates=") (pprint candidates))
              ;; Now select a method if no match, generate a gap filler
              selected (select-candidate candidates) ;+++ generate a gap filler if necessary +++
              ;; Next generate the correct call for the chosen methods
              actions (compile-calls selected this-goal queries)
              bindings nil
              - (println "actions=" actions)
              subgoals (apply concat (map (fn [[call prec]]
                                            (simplify-condition prec))
                                          actions))
              outstanding-goals  (remove nil? (concat subgoals outstanding-goals))]
          (println "selected=" selected "actions=" actions "subgoals=" subgoals)
          (if (empty? outstanding-goals)
            (concat actions complete-plan)
            (recur outstanding-goals (concat actions complete-plan))))))))

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
  []
  (let [root-objects (rtm/get-root-objects)
        ;;- (println "root-objects=" root-objects)
        controllable-objects (rtm/get-controllable-objects)
        ;;- (println "controllable-objects=" root-objects)
        [pclass goal-conds] (rtm/goal-post-conditions)
        ;;- (do (println "Root PCLASS=" pclass "GOAL:")(pprint goal))
        actions (plan root-objects controllable-objects pclass (simplify-condition goal-conds))
        ;; +++ Now put the call into the solution
        compiled-calls (scompile-call-sequence (seq (map first actions)))
        ]
    ;;(pprint actions)
    compiled-calls))

;;; (solveit)




;;; Fin
