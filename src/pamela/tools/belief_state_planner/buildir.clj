;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.buildir
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
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.evaluation :as eval]
            ;[pamela.tools.belief-state-planner.simplify :as simp :refer :all]
            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.buildir)

(def ^:dynamic verbosity 0)

(def ^:dynamic *printdebug* false) ; false

(defn set-verbosity
  [n]
  (def ^:dynamic verbosity n))

(defn nyi
  [text]
  (if (> verbosity 2) (println "NYI called with: " text))
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

(defn describe-goal
  [agoal]
  (if (= (first agoal) :thunk)
    (pprint [:thunk (second agoal) (.variable (nth agoal 2))])
    (pprint agoal)))

(defn describe-goals
  [goals]
  (if (> verbosity 0) (println))
  (if (> verbosity 0) (println "***Current outstanding goals:"))
  (if (> verbosity 0)
    (doseq [agoal goals]
      (describe-goal agoal))))

;;; Args are evaluated from the standpoint of the root
(defn make-args-map-and-args
  [formals actuals wrtobject]
  (let [adjactuals (if (> (count actuals) (count formals))
                     (do (if (> verbosity 0) (println "+++ Dropping first actual (superfluous)"))
                         (if (> verbosity 3) (println "dropped actual=" (first actuals) "remaining =" (rest actuals)))
                         (rest actuals))
                     actuals)]
    (if (not (= (count formals) (count adjactuals)))
      (irx/error  "Wrong Number of Arguments in: make-args-map-and-args formals=" formals " actuals=" adjactuals))
    (let [- (if (> verbosity 2) (println "*** make-args-map-and-args: " adjactuals "wrtobject=" wrtobject))
          argsmap (into {} (map (fn [f a] [f a]) formals adjactuals))]
      (if (> verbosity 2) (println "argsmap=" argsmap))
      [adjactuals argsmap])))


(defn get-references-from-value
  [val]
  (cond (keyword? val) nil
        (global/RTobject? val) [[:foo val]])) ; unfinished

(defn get-references-from-expression
  "Generate the ir for the expression and the mapping from the argument name to the expression and its IR."
  ;; +++ currently only produces the IR and not the mapping.
  [expn]
  ;; (println "In get-references-from-expression, expn=" expn)
  (cond (= (first expn) :field) [expn] ;; [(ir-field-ref [(second expn)])]
        (= (first expn) :value) (get-references-from-value (second expn))
        (= (first expn) :arg) [[:arg-ref (first expn) (second expn)]] ; +++ placeholder
        (= (first expn) :mode-of) nil
        :otherwise nil))

(defn get-references-from-condition
  [condition]
  (if (> verbosity 2) (println "Entering get-references-from-condition, condition=" condition))
  (let [result (case (first condition)
                 :thunk
                 (do
                   (if (> verbosity 3)
                     (println "get-references-from-condition :thunk case -" condition))
                   (into [] (map (fn [ref] [:thunk ref (nth condition 2)])
                                 (get-references-from-condition (nth condition 1)))))

                 (:equal :same :notequal :notsame)
                 (into [] (apply concat
                                 (map (fn [expn] (get-references-from-expression expn))
                                      (rest condition))))

                 (:and :or)
                 (into [] (apply concat
                                 (map (fn [subcond] (get-references-from-expression subcond))
                                      (rest condition))))

                 (do (irx/error "Unhandled case in get-references-from-condition: " condition)
                     nil))]
    (if (> verbosity 2)
      (println "exiting get-references-from-condition, condition=" condition "=" result))
    result))

(defn get-object-root-name
  [object]
  (if (global/RTobject? object)
    (let [nameparts (string/split (.variable object) #"\.")
          rootname (if (not (empty? (rest nameparts)))
                     (symbol (str (string/join "." (rest nameparts))))
                     nil)]
      (if (> verbosity 3)
        (println "get-object-root-name object=" object "rootname=" rootname))
      (if rootname [:thunk [:field rootname] (global/root-object)]))
    "error-non-rtobject-value-passed-to-get-object-root-name"))

;;; (get-object-root-name "/world.foo.bar")

(defn thunk?
  [thing]
  (and (sequential? thing) (= (first thing) :thunk)))

(defn get-queries-in
  [goal-fragment]
  (cond
      (thunk? goal-fragment)
      (let [rootname (get-object-root-name (nth goal-fragment 2))]
        (if rootname (cons rootname [goal-fragment]) [goal-fragment]))

      (and (vector? goal-fragment) (= (first goal-fragment) :arg-field))
      (let [rootname (get-object-root-name (nth goal-fragment 1))]
        (if rootname (cons rootname [goal-fragment]) [goal-fragment]))

      (number? goal-fragment) ; +++ probably need a more general 'value' case here
      [[:value goal-fragment]]

      :otherwise
      [goal-fragment]))

(defn find-queries-in-goal
  [querypart goal]
  (let [queries (case (first goal)
                  :thunk (do
                           ;;(println "find-queries-in-goal :thunk case -" goal)
                           ;;(cons (get-object-root-name (nth goal 2))
                           (find-queries-in-goal querypart (nth goal 1)))
                  (:equal :same)
                         (cond (= querypart (nth goal 1)) (get-queries-in (nth goal 2))
                               (= querypart (nth goal 2)) (get-queries-in (nth goal 1))
                               :otherwise [])
                  (:notequal :notsame)
                         (cond (= querypart (nth goal 1)) (get-queries-in (nth goal 2))
                               (= querypart (nth goal 2)) (get-queries-in (nth goal 1))
                               :otherwise [])
                  [:unhandled-case-in-find-query-in-goal goal])]
    (if (> verbosity 3)
      (println "find-queries-in-goal - querypart=" querypart "goal=" goal "queries=" queries))
    queries))


(defn get-goal-references
  [query goal]
  (let [result (find-queries-in-goal (second query) goal)]
    (if (> verbosity 3)
      (println "get-goal-references query=" query "goal=" goal "result=" result))
    result))

;;; A call comes 'from' the root 'to' the controllable.
(defn compile-arglist
  "Returns [argsmap actuals]."
  [action goal query wrtobject]
  (if (> verbosity 3)
    (do
      (println "compile-arglist action=" (.mname (.methodsig action))
                               " query=" query " and goal:")
      (describe-goal goal)))
  (let [pcls (.pclass action)
        msig (.methodsig action)
        argnames (.arglist msig)
        mname (.mname msig)
        -     (if (> verbosity 3) (println "class/method/argnames=" pcls mname argnames))
        returnvals
        (cond
          ;; Handle arglist by query type
          (= query [:any [:arg-mode]])
          ;; Here we are looking to provide the object being affected
          (make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal)) wrtobject)

          :otherwise
          (make-args-map-and-args argnames (map irx/compile-reference (get-goal-references query goal)) wrtobject)

          #_(let [amap (match-goal-query? goal query)]
              (make-args-map-and-args argnames (map (fn [arg]
                                                      (irx/compile-reference (get amap arg)))
                                                    argnames)))
          #_(make-args-map-and-args argnames (map irx/compile-reference (get-references-from-condition goal))))]
    (if (> verbosity 3) (println "compile-arglist returns:" returnvals))
    returnvals))

(defn compile-controllable-object
  [action goal query]
  (let [objs (rtm/get-root-objects-of-type (.pclass action))
        object (first objs)]  ;+++ what about if there are multiple such objects? +++
    object))

(defn replace-args-with-bindings
  [mname condit argmap]
  (if (> verbosity 2) (println "Entering replace-args-with-bindings - Method=" mname "condit=" condit " argmap=" argmap))
  (let [replaced (if (not (vector? condit))
                   condit
                   (case (first condit)
                     :call (into [(nth condit 0) (nth condit 1) (nth condit 2)]
                                 (map (fn [subexp]
                                        (replace-args-with-bindings mname subexp argmap))
                                      (rest (rest (rest condit)))))

                     :arg (get argmap (second condit))

                     :arg-field
                     (let [object (get argmap (nth condit 1))]
                       (if (thunk? object)
                         (case (first (nth object 1))
                           :field
                           [:arg-field (eval/deref-field (rest (nth object 1)) (nth object 2) :reference) (nth condit 2)]

                           :arg-field
                           (eval/deref-field (rest (nth object 1)) :reference)

                                        ;+++ possibly add other cases here
                           [:arg-field [:arg-field (nth object 2) (nth object 1)] (nth condit 2)])
                         [:arg-field object (nth condit 2)]))

                     :lookup-propositions
                     [:lookup-propositions
                      (into [] (map (fn [prop-pat]
                                      (let [[lu where [pn arg1 arg2]] prop-pat]
                                        [lu where [pn
                                                   (replace-args-with-bindings mname arg1 argmap)
                                                   (replace-args-with-bindings mname arg2 argmap)]]))
                                    (nth condit 1)))
                      (let [condition (nth condit 2)]
                        (replace-args-with-bindings mname condition argmap))]

                     (:and :or :not :equal :same :notequal :notsame)
                     (into [(first condit)]
                           (map (fn [subexp]
                                  (replace-args-with-bindings mname subexp argmap))
                                (rest condit)))
                     ;; Default
                     condit))]
    (if (> verbosity 2)
      (println "replace-args-with-bindings - condit=" condit " argmap=" argmap " replaced=" replaced))
    replaced))

;;; Format of an action is: [pclass (method-name [preconditions][postconditions] (probability) (list-of-args))]
(defn compile-call
  "Given a call, construct the IR for the call and return also the prerequisites
   and the bindings, as a vector [ir-call vector-of-prerequisites vector-of-bindings]."
  [action goal query root-objects wrtobject]
  (if (> verbosity 2)
    (do (println "action=" action " query=" query " and goal:")
        (describe-goal goal)))
  (let [[args argmap] (compile-arglist action goal (second query) wrtobject)  ;+++ kludge "second" +++ was (first root-objects)
        object (compile-controllable-object action goal (second query))] ;+++ kludge "second"
    [(ir-method-call (ir-field-ref [object (irx/.mname (.methodsig action))]) args)
     (replace-args-with-bindings (irx/.mname (.methodsig action)) (irx/.prec (.methodsig action)) argmap)
     (replace-args-with-bindings (irx/.mname (.methodsig action)) (irx/.postc (.methodsig action)) argmap)]))

(defn compile-calls
  [actions goal queries root-objects rtos]
  (if (> verbosity 2)
    (println "compile-calls: actions=" actions "goal=" goal "queries=" queries "rtos=" rtos))
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
  (if (> verbosity 3) (pprint calls))
  (let [;; scalls (sanitize-calls calls)
        sequence (ir-sequence (into [] calls))
        - (if (> verbosity 3) (do (println "sequence:") (pprint sequence)))
        code-source-fragment
        (with-out-str
            (println (pup/unparse-fn sequence)))]
    code-source-fragment))

(defn compile-action-to-pamela
  [action]
  (let [[call post] action
        {mref :method-ref
         args :args} call
        {names :names} mref
        argvals (map (fn [anarg]
                       (let [value (eval/evaluate-reference nil anarg nil nil nil nil)]
                         (cond (and (sequential? value)
                                    (= (first value) :value)
                                    (get (second value) :variable))
                               (symbol (apply str (rest (string/split (get (second value) :variable) #"\."))))

                               :otherwise value)))
                     args)]
    (concat
     (list (symbol (str (first names)  "." (second names))))
     argvals)))

(defn compile-actionlist-to-pamela
  [action-list]
  (map (fn [anaction] (compile-action-to-pamela anaction)) action-list))

(defn compile-actions-to-pamela
  [action-list]
  (cons 'sequence (compile-actionlist-to-pamela action-list)))
