;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.simplify
  "Planner Simplify Expression"
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
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.evaluation :as eval]
            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.simplify)

(def ^:dynamic verbosity 0)

(def ^:dynamic *printdebug* false) ; false

(defn set-verbosity
  [n]
  (def ^:dynamic verbosity n))

(defn nyi
  [text]
  (if (> verbosity 2) (println "NYI called with: " text))
  nil)

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
             ;; Handle case where expression of not simplifies to a conjunction.
             (case (count exps)
               0 :true
               1 (first exps)
               (into [:and] exps)))
      ;; OR ~(Happy OR Sad) = ~Happy AND ~Sad
      :or (into [:and] (map (fn [sc] (simplify-negate sc wrtobject)) (rest condit)))
      ;; AND - ~(Happy AND Sad) = ~(~Happy OR ~Sad)
      :and (simplify-negate (into [:or] (map (fn [sc] (simplify-negate sc wrtobject))
                                             (rest condit)))
                            wrtobject)
      [:not condit])))



;;; [:and [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]]

(defn conjunctive-list
  [condit wrtobject]
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
  (let [evaluated (eval/evaluate-reference wrtobject exprn nil nil nil nil)
        bound-value (if (and (lvar/is-lvar? evaluated) (lvar/is-bound-lvar? evaluated)) (lvar/deref-lvar evaluated) false)
        - (if (> verbosity 3) (println "In un-lvar-expression with exprn=" exprn "evaluates to " evaluated))
        - (if (> verbosity 3) (if bound-value (println "****" (lvar/.name evaluated) "=" bound-value)))
        result (if (sequential? exprn)
                 (case (first exprn)
                   :field (if bound-value [:field [:value bound-value]] exprn) ; was [:field [:value bound-value]] [:value bound-value]
                   :mode-of exprn                    ; Perhaps allow the class and the value to be lvared?+++
                   :arg-field exprn
                   exprn)
                 exprn)]
    (if (not (= exprn result)) (if (> verbosity 3) (println "LVAR binding applied: was: " exprn "now: result")))
    result))


(defn print-condition-tersely
  [condition]
  (if (= (first condition) :thunk)
    (do
      (print "[:thunk ")
      (pprint (second condition))
      (println (.variable (nth condition 2)) "]"))
    (pprint condition))
  nil)

(defn simplify-condition
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit wrtobject]
  (if (> verbosity 3) (println "In simplify condition with: " condit))
  (if (not (or (list? condit) (vector? condit)))
    (list condit)
    (let [result (case (first condit)
                   :thunk (list
                           (into [:thunk] (into (into [] (simplify-condition (nth condit 1) (nth condit 2))) [(nth condit 2)])))

                   :equal (list
                           [:equal
                            (un-lvar-expression (nth condit 1) wrtobject)
                            (un-lvar-expression (nth condit 2) wrtobject)])

                   :same (list
                           [:same
                            (un-lvar-expression (nth condit 1) wrtobject)
                            (un-lvar-expression (nth condit 2) wrtobject)])

                   ;; NOT negate the simplified subexpression
                   :not (conjunctive-list (simplify-negate (second condit) wrtobject) wrtobject)

                   ;; AND return the simplified parts as a list.
                   :and (apply concat (map (fn [sc] (simplify-condition sc wrtobject)) (rest condit)))

                   ;; OR - Happy OR Sad = ~(~Happy AND ~Sad)
                   :or (conjunctive-list (simplify-negate (into [:and]
                                                                (map (fn [sc]
                                                                       (simplify-negate sc wrtobject))
                                                                     (rest condit)))
                                                          wrtobject)
                                         wrtobject)

                   :field [:value (un-lvar-expression condit wrtobject)]

                   :lookup-propositions
                   (do
                     ;;(println "*** FOUND lookup-propositions-here!!!" condit)
                     [condit])

                   [condit])
          simpres (remove (fn [x] (= x true)) result)]
      ;; (println "simplified=" result "simpres=" simpres)
      (if (> verbosity 3)
        (do (println "In simplify-condition: simpres: ")
            (print-condition-tersely simpres)))
      simpres)))

(defn simplify-cond-top-level
  [condit wrtobject]
  (if (> verbosity 3) (println "In Simplify with condit=" condit " wrtobject=" (.variable wrtobject)))
  (let [simplified (simplify-condition condit wrtobject)
        terms (count simplified)]
    (if (> terms 1)
      simplified ;(list (into [:and] simplified))
      simplified)))

;;; (simplify-condition '[:and [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])
;;; (simplify-condition '[:or [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]])
