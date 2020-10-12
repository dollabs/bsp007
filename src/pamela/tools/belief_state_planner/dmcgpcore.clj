;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.dmcgpcore
  "DOLL Monte-Carlo Generative Planner"
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
            [random-seed.core :refer :all]
            [pamela.tools.belief-state-planner.runtimemodel :as rtm]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.expressions :as dxp]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.simplify :as simp :refer :all]
            [pamela.tools.belief-state-planner.buildir :as bir :refer :all]
            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.dmcgpcore)

(defrecord MethodQuery [pclass methodsig rootobject rto])

(def ^:dynamic available-actions nil)
(def ^:dynamic plan-fragment-library nil)
;(def ^:dynamic verbosity 0)

;(def ^:dynamic *printdebug* false) ; false

;; (defn set-verbosity
;;   [n]
;;   (def ^:dynamic verbosity n))

(defn nyi
  [text]
  (if (> verbosity 2) (println "NYI called with: " text))
  nil)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Virtual states

(defn snapshot-modeled-state
  "Create a snapshot of the current state"
  []
  (nyi "snapshot-modeled-state"))

(defn reset-modeled-state
  [virtual-state-snapshot]
  (nyi "reset-modeled-state"))



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
  (let [- (if (> verbosity 0) (println "New Sample"))
        ;;  Snapshot the state in order to be able to replay for other samples.
        virtual-state-snapshot (snapshot-modeled-state)
        ;; For each goal constraint, find an action likely to achieve it chosen by Monte-Carlo weighted random selection.
        actions (seq (map (fn [goal] (find-an-action-to-achieve goal goal-constraints)) goal-constraints))
        - (if (> verbosity 0) (println "Top-level-actions: " actions)) ; debugging statement
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

(defn generate-lookup-from-condition
  "Translate a goal condition into lookups for the inverse influence table."
  [pclass condition]

  (if (> verbosity 3)
    (do (println "In generate-lookup-from-condition: pclass=" pclass "condition: ")
        (print-condition-tersely condition)))

  (if (sequential? condition)               ;atomic conditions = no influence
    (case (first condition)
      :thunk (let [[cond rto] (rest condition)] (generate-lookup-from-condition pclass cond))
      (:equal :same)
             (let [[arg1 arg2] (rest condition)
                   arg1 (if (value? arg1) (second arg1) arg1)
                   arg2 (if (value? arg2) (second arg2) arg2)]
               (cond (and ; This doesn't work becquse we want to be qble to use finite values
                      (or (rtm/RTobject? arg1) (= (first arg1) :field))
                      (and (vector? arg2) (= (first arg2) :mode-of)))
                     (list [condition [:any [:arg-mode]]])

                     (and
                      (or (rtm/RTobject? arg2) (and (vector? arg2) (= (first arg2) :field)))
                      (and (vector? arg1) (= (first arg1) :mode-of)))
                     (list [condition [:any [:arg-mode]]])

                     (rtm/RTobject? arg1)
                     (list [condition [:object arg1]]) ;+++ surely we want to get both cases

                     (rtm/RTobject? arg2)
                     (list [condition [:object arg2]])

                     (and (vector? arg1) (= (first arg1) :field))
                     (list [condition [pclass [:field (second arg1)]]]) ;+++ surely we want to get both cases

                     (and (vector? arg2) (= (first arg2) :field))
                     (list [condition [pclass [:field (second arg2)]]])

                     (and (vector? arg1) (= (first arg1) :arg-field))
                     (list [condition [pclass [:arg-field (second arg1)]]])

                     (and (vector? arg2) (= (first arg2) :arg-field))
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
                        [:same [:field handholds] [:arg object]]
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
  (cond (and (sequential? (nth postconds 1)) (= (first (nth postconds 1)) :arg))
        (nth postconds 1)

        (and (sequential? (nth postconds 2)) (= (first (nth postconds 2)) :arg))
        (nth postconds 2)

        (and (sequential? (nth postconds 1)) (= (first (nth postconds 1)) :arg-field))
        (nth postconds 1)

        (and (sequential? (nth postconds 2)) (= (first (nth postconds 2)) :arg-field))
        (nth postconds 2)

        :otherwise
        nil))

(defn nonargpart
  [postconds]
  (if (not (and (sequential? (nth postconds 1)) (= (first (nth postconds 1)) :arg)))
    (nth postconds 1)
    (if (not (and (sequential? (nth postconds 2)) (= (first (nth postconds 2)) :arg)))
      (nth postconds 2)
      nil)))

;;; +++ we need to handle all of the cases here +++
(defn match-goal-query-aux
  [goal postconds]
  (if (> verbosity 2) (println "in match-goal-query-aux with (" goal "," postconds ")"))
  (cond
    (= goal postconds)
    (list (first goal) (first postconds))

    (= (first goal) (first postconds))
    (case (first goal)
      (:equal :same) ;+++ is this right?  Does :same belong here?
             (let [argcondpart (argpart postconds)
                   -  (if (> verbosity 3) (println "argcondpart=" argcondpart))
                   matchcondpart (nonargpart postconds)
                   - (if (> verbosity 3) (println "matchcondpart=" matchcondpart))
                   matchresult (if (and argcondpart matchcondpart)
                                 (if (= matchcondpart (nth goal 1))
                                   (into {} (list [(second argcondpart) (nth goal 2)]))
                                   (if (= matchcondpart (nth goal 2))
                                     (into {} (list [(second argcondpart) (nth goal 1)]))
                                     nil)))]
               (if (> verbosity 3) (println "match " matchcondpart " with " goal " goal =" matchresult))
               matchresult)

      (do (if (> verbosity 0) (println "match-goal-query-aux unhandled case 1: goal=" goal " posts=" postconds))
          nil))

    :otherwise
    (do (if (> verbosity 0)
          (println "match-goal-query-aux unhandled case 2: goal=" goal " posts=" postconds))
      nil)))

(defn match-goal-query?
  [goal query]
  (let [postconds (irx/.postc (.methodsig query))
        amatch (case (first postconds)
                 (:equal :same)
                   (match-goal-query-aux goal postconds)
                 :and
                   (some (fn [apost] (match-goal-query-aux goal apost)) (rest postconds))
                 (do (if (> verbosity 0)
                       (println "match-goal-query? unhandled case: goal=" goal " posts=" postconds))
                     nil))]
    (if (> verbosity 2)
      (println "match-goal-query? goal=" goal "query=" query "posts=" postconds "amatch=" amatch))
    amatch))

(defn verify-candidate
  [acand]
  (let [[goal signature cmethods rootobj rtobj] acand
        rtotype (get rtobj :type)
        - (if (> verbosity 2) (println "verify-candidate goal=" goal " sign=" signature " methods=" cmethods))
        methods (rtm/get-controllable-methods) ; Cache this, no need to recompute all the time.+++
        _ (if (> verbosity 2) (do (println "Controllable-methods:") (pprint methods)))
        ;; Step 1: Filter out methods that dont match either by pclass or by name
        matchingmethods (remove nil? (map (fn [[pclass pmethod rtobj]]
                                            (if (and (= pclass rtotype)
                                                     (or (= (first signature) :any)
                                                         ;;(= (first signature) (irx/.mname pmethod))
                                                         (= (first signature) (rtm/get-root-class-name)))
                                                     (some #{(irx/.mname pmethod)} cmethods))
                                              (do
                                                (if (> verbosity 3) (println "pc= " pclass " pm=" (.mname pmethod)))
                                                (MethodQuery. pclass pmethod rootobj rtobj))
                                              nil))
                                          methods))
        _ (if (> verbosity 2) (do (println "matchingmethods1:") (pprint matchingmethods)))
        desired-mode (if (mode-signature signature) (get-desired-mode goal) nil)
        _ (if (> verbosity 2) (if desired-mode (println "matchingmethods1b - desired-mode=" desired-mode)))

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
        _ (if (> verbosity 2) (do (println "matchingmethods2:") (pprint matchingmethods)))
        ]
    matchingmethods))

;;; Non learning version +++ replace with learning version when fixed!
(defn select-candidate
  [cands]
  (if (not (empty? cands)) (list (rand-nth cands)) nil))

#_(defn substitute-bindings
  [condit bindings]
  ;; This call is no longer needed since we do substitution earlier.
  ;(println "in substitute-bindings with: " condit)
    condit)
;;; Why not just push all of this into rtm/evaluate?
;;; Always return true or false, if true, may bind lvars

;;; This is the non-learning version to begin with - learning version still needs debugging
(defn mcselect
  [choices]
  (rand-nth choices))

(defn select-and-bind2
  [arg1 arg2 matches]
  (let [num-matches (count matches)]
    (if (> verbosity 3) (println "In select-and-bind2: num-matches=" num-matches "here: " matches))
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
            arg1r (if (and (rtm/is-lvar? arg1) (rtm/is-bound-lvar? arg1)) (rtm/deref-lvar arg1) arg1)
            arg2r (if (and (rtm/is-lvar? arg2) (rtm/is-bound-lvar? arg2)) (rtm/deref-lvar arg2) arg2)
            arg1 (if (and false (string? arg1r)) (symbol arg1r) arg1r)
            arg2 (if (and false (string? arg2r)) (symbol arg2r) arg2r)]
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

(declare condition-satisfied?)

(defn compute-prop-matches
  "For a binary proposition [:prop arg1 arg2] product arglist for find-binary-propositions"
  [wrtobject propn]
  (let [[_ lookupin [pname a1 a2]] propn]
    (if (> verbosity 2) (println "In compu-prop-matches with pname=" pname "a1=" a1 "a2=" a2))
    (let [arg1 (rtm/evaluate wrtobject "???" a1 nil nil nil nil)
          arg2 (rtm/evaluate wrtobject "???" a2 nil nil nil nil)
          ;;_ (println "arg1=" arg1 "arg2=" arg2)
          arg1-unbound-lvar (and (rtm/is-lvar? arg1) (not (rtm/is-bound-lvar? arg1)))
          arg2-unbound-lvar (and (rtm/is-lvar? arg2) (not (rtm/is-bound-lvar? arg2)))
          ;; Dereference bound LVARS
          arg1 (if (and (rtm/is-lvar? arg1) (rtm/is-bound-lvar? arg1)) (rtm/deref-lvar arg1) arg1)
          arg2 (if (and (rtm/is-lvar? arg2) (rtm/is-bound-lvar? arg2)) (rtm/deref-lvar arg2) arg2)]
      ;;(println "arg1=" arg1 "arg1-unbound-lvar=" arg1-unbound-lvar)
      ;;(println "arg2=" arg2 "arg2-unbound-lvar=" arg2-unbound-lvar)
      (let [results
            (cond ;; There are 4 cases, one bound, the other bound, both bound, neither bound
              (not (or arg1-unbound-lvar arg2-unbound-lvar)) ; both bound
              [arg1 arg2 (bs/find-binary-propositions-matching #{arg1} nil #{pname} nil #{arg2} nil)]

              (and arg1-unbound-lvar (not arg2-unbound-lvar)) ; arg2 bound
              [arg1 arg2 (bs/find-binary-propositions-matching nil nil #{pname} nil #{arg2} nil)]

              (and (not arg1-unbound-lvar) arg2-unbound-lvar) ; arg1 bound
              [arg1 arg2 (bs/find-binary-propositions-matching #{arg1} nil #{pname} nil nil nil)]

              (and arg1-unbound-lvar arg2-unbound-lvar) ; This is a strange request, but not illegal
              [arg1 arg2 (bs/find-binary-propositions-matching nil nil #{pname} nil nil nil)]

              :otherwise (irx/error "compûte-prop-matches: can't get here, arg1=" arg1 " arg2=" arg2))]
        (if (> verbosity 2) (println "compute-prop-matches results=" results))
        results))))

(defn lookup-propositions-aux
  "Recurse down the propositions to find compatible matches that satisfy the condition"
  [pvec path wrtobj condition pmatches]
  (if (empty? pvec)
    (do (if (> verbosity 2)
          (println "found-candidate path=" path "constraint=" condition "="
                   (condition-satisfied? condition wrtobj) "wrtobject=" wrtobj))
        (if (condition-satisfied? condition wrtobj) (reset! pmatches (conj @pmatches path)))) ; Success case
    (let [[arg1 arg2 matches] (compute-prop-matches wrtobj (first pvec))] ; [a1 a2 matches]
      (when (not (empty? matches))      ; continue if we found at least one match
        (doseq [m matches]
          ;; bind the lvars for a1 and a2 and recurse
          (let [{ptype :ptype, subj :subject, obj :object} m
                ubarg1 (if (and (rtm/is-lvar? arg1) (not (rtm/is-bound-lvar? arg1)))
                         (do (rtm/bind-lvar arg1 subj) arg1))
                ubarg2 (if (and (rtm/is-lvar? arg2) (not (rtm/is-bound-lvar? arg2)))
                         (do (rtm/bind-lvar arg2 subj) arg2))]
            (lookup-propositions-aux (rest pvec) (conj path [arg1 arg2 m]) wrtobj condition pmatches)
            ;; Any lvars bound on the way in are unbound on the way out
            (if ubarg1 (rtm/unbind-lvar ubarg1))
            (if ubarg2 (rtm/unbind-lvar ubarg2))))))))

(defn select-and-bind2-n
  "Given a sequence of n proposition bindings that satisfy the condition, select one and make all necessary bindings"
  [pmatches]
  (let [num-matches (count pmatches)]
    (if (> verbosity 4) (println "In select-and-bind2-n: num-matches=" num-matches "here: " pmatches))
    (if (empty? pmatches)
      false                                ; Nothing found, no variables bound : FAIL
      (let [selection (mcselect pmatches)] ; selection is a path of propositions one entry for each proposition
        (doseq [[arg1 arg2 aprop] selection]
          (let [{ptype :ptype, subj :subject, obj :object} aprop]
            (when (and (rtm/is-lvar? arg1) (rtm/is-unbound-lvar? arg1))
              ;; (println "Binding " arg1 "to" subj)
              (rtm/bind-lvar arg1 subj))
            (when (and (rtm/is-lvar? arg2) (rtm/is-unbound-lvar? arg2))
              ;; (println "Binding " arg2 "to" obj)
              (rtm/bind-lvar arg2 obj))))
        selection))))

(defn lookup-propositions
  "Find all possible sequences of n propositions that satisfy the condition, select one and make bindings"
  [wrtobj condit]
  ;; (println "In lookup-propositions with:" condit)
  (let [pmatches (atom [])
        [type pvec constraint] condit] ; [:lookup-propositions vector-of-propositions condition]
    (lookup-propositions-aux pvec [] wrtobj constraint pmatches)
    ;; Here any matches will be in pmatches, no bindings will have been made.  Pick one and bid accordingly.
    ;;; Always return true or false, if true, may bind lvars
    (select-and-bind2-n @pmatches)))

(defn condition-satisfied?
  [condit wrtobject]
  ;;(println "In condition-satisfied? with condit=" condit)
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
        (if (> verbosity 3) (println "In condition-satisfied? with (= "
                                     (with-out-str (print (nth condit 1)))
                                     (with-out-str (print (nth condit 2)))
                                     ")"))
        (let [first-expn (rtm/evaluate  wrtobject "???" (nth condit 1) nil nil nil nil)
              first-expn (if (rtm/is-lvar? first-expn) (rtm/deref-lvar first-expn) first-expn)
              second-expn (rtm/evaluate wrtobject "???" (nth condit 2) nil nil nil nil)
              second-expn (if (rtm/is-lvar? second-expn) (rtm/deref-lvar second-expn) second-expn)]
          (if (> verbosity 3) (println "(= "
                                       (with-out-str (print (nth condit 1))) "=" first-expn
                                       (with-out-str (print (nth condit 2))) "=" second-expn
                                       ")"))
          (= first-expn second-expn)))
      ;; SAME -
      :same ;(y-or-n? (str "(condition-satisfied? " (with-out-str (print condit)) ")"))
      (do
        (if (> verbosity 3) (println "In condition-satisfied? with (= "
                                     (with-out-str (print (nth condit 1)))
                                     (with-out-str (print (nth condit 2)))
                                     ")"))
        (let [first-expn (rtm/evaluate-reference  wrtobject (nth condit 1) nil nil nil nil)
              first-expn (if (rtm/is-lvar? first-expn) (rtm/deref-lvar first-expn) first-expn)
              second-expn (rtm/evaluate-reference wrtobject (nth condit 2) nil nil nil nil)
              second-expn (if (rtm/is-lvar? second-expn) (rtm/deref-lvar second-expn) second-expn)]
          (if (> verbosity -1) (println "(same "
                                       (with-out-str (print (nth condit 1))) "=" first-expn
                                       (with-out-str (print (nth condit 2))) "=" second-expn
                                       ")"))
          (= first-expn second-expn)))
      :call
      (let [plant (nth condit 1)
            names (nth condit 2)
            args (doall (map (fn [arg]
                               (rtm/evaluate wrtobject "???" arg nil nil nil nil))
                             (rest (rest (rest condit)))))]
        (cond (= plant 'dmcp) ;+++ dmcp handled specially
              (internal-condition-call plant (first names) args)

              :otherwise (do (irx/break "CALL: plant=" plant " names=" names " args=" args) true)))

      :lookup-propositions
      (lookup-propositions wrtobject condit)

      (irx/error "(condition-satisfied? " condit ")"))))

(defn plan-generate
  [root-objects controllable-objects pclass list-of-goals max-depth]
  (loop [goals list-of-goals        ; List of things to accomplish
         ;; wrtobject (second (first root-objects))
         complete-plan []           ; List of actions collected so far
         depth 0]
    (if (>= depth max-depth)
      (if (> verbosity 0) (do (println "DMCP: Aborting sample because maximum depth of " max-depth " has been reached.")
                              (println "************************************************************************")
                              nil))
      (let [goals (apply concat (map (fn [agoal] (simplify-cond-top-level agoal (second (first root-objects)))) goals))
            - (if (> verbosity 0)
                (do (println "Current outstanting goals:"))
                (describe-goals goals))
            this-goal (first goals)        ; We will solve this goal first
            rootobject (second (first root-objects))
            - (if (> verbosity 0)
                (do (println "Solving for:")
                    (describe-goal this-goal)))
            outstanding-goals (rest goals)] ; Afterwards we will solve the rest

        (rtm/start-plan-bind-set)

        (if (condition-satisfied? this-goal rootobject)
          (if (empty? outstanding-goals)
            (do (if (> verbosity 0) (println "***Solution found!"))
                (if (> verbosity 1)
                  (do (pprint complete-plan)
                      (println "************************************************************************")))
                complete-plan)                 ; The last outstanding goal was satisfied, return the completed plan SUCCESS
            (recur outstanding-goals complete-plan depth)) ; Continue until we reach an unsatisfied goal
          ;; Now we have a goal that requires effort to solve.

          (do
            (rtm/stop-plan-bind-set)

            (let [queries (generate-lookup-from-condition pclass this-goal)
                  - (if (> verbosity 1) (println "Root query=" queries))
                  iitab (rtm/inverted-influence-table)
                  - (if (> verbosity 2) (println "iitab=" iitab))
                        candidates (apply concat (map (fn [[agoal aquery]]
                                                        (map (fn [[coid ctrlobj]]
                                                               [agoal aquery (get iitab aquery) rootobject ctrlobj])
                                                             controllable-objects))
                                                      queries))    ;+++ need to handle nested queries+++
                        _ (if (> verbosity 1) (do (println "candidates=") (pprint candidates)))
                        candidates (apply concat (map (fn [cand] (verify-candidate cand)) candidates))
                        _  (if (> verbosity 1) (do (println "good candidates=") (pprint candidates)))
                        ;; Now select a method if no match, generate a gap filler
                        selected (select-candidate candidates)] ;+++ generate a gap filler if necessary +++
                  (if selected                                ; If we have found an action to try prepare it, otherwise we fail
                    (let [rtos (map (fn [anmq] (.rto anmq)) selected)
                          actions (compile-calls selected this-goal queries root-objects rtos) ;
                          _ (if (> verbosity 1) (println "ACTIONS=" actions))
                          subgoals (apply concat (map (fn [[call prec] rto]
                                                        (if (not (rtm/RTobject? rto)) (irx/error "not an RTobject: " rto))
                                                        (map (fn [conj] [:thunk conj rto])
                                                             (simplify-cond-top-level prec rto)))
                                                      actions rtos))
                          ;;subgoals (apply concat (map (fn [[call prec]] (simplify-cond-top-level prec nil)) actions))
                          outstanding-goals  (remove nil? (concat subgoals outstanding-goals))]

                      (if (> verbosity 4) (do (println "selected=") selected))
                      (if (> verbosity 2) (println "actions=" actions))
                      (if (> verbosity 2) (println "subgoals=" subgoals))
                      (let [plan-part (concat actions complete-plan)]
                        (if (> verbosity 1) (println "ACTION-ADDED-TO-PARTIAL-PLAN: " actions))
                        (if (empty? outstanding-goals)
                          plan-part             ; Current action has no prerequisited (rare) and there are none outstanding SUCCESS
                          (recur outstanding-goals plan-part (+ 1 depth)))))
                    (do
                      (if (> verbosity 0) (println "DMCP: sample failed, depth=" depth))
                      (if (> verbosity 0)
                        (do (println "Couldn't find an action to solve for: ")
                            (describe-goal this-goal)))
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
;;;   [:same [:field handholds] [:arg object]]
;;;   [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])

(defn solveit
  "Generate a plan for the goals specified in the model."
  [& {:keys [samples max-depth rawp] :or {samples 10 max-depth 10 rawp false}}]
  (if (> verbosity 0) (println "DMCP: solving with " samples "samples, max-depth=" max-depth))
  (loop [solutions ()
         sampled 0]
    (if (and (> verbosity 1) (> sampled 0))
      (println "DMCP: " (count solutions) "found so far out of " sampled " samples."))
    (if (>= sampled samples)
      (if (not (empty? solutions))                         ; We have done enough, return what we have
        (do
          (if (> verbosity 0) (println "Completed DMCP: " (count solutions) "found out of " sampled " samples."))
          (doall solutions))
        nil)      ; And it turns out that we didn't find any solutions. nil result signifies failure
      (let [root-objects (rtm/get-root-objects)
            ;; - (println "root-objects=" root-objects)
            controllable-objects (rtm/get-controllable-objects)
            ;; - (println "controllable-objects=" controllable-objects)
            [pclass goal-conds] (rtm/goal-post-conditions)
            - (if (> verbosity 0) (do (println "Root PCLASS=" pclass "GOAL:")(pprint goal-conds)))
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
