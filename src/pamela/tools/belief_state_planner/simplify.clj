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
            [pamela.tools.belief-state-planner.imagine :as imag]
            [pamela.tools.belief-state-planner.evaluation :as eval]
            [pamela.tools.belief-state-planner.coredata :as global]

            [pamela.tools.belief-state-planner.prop :as prop]
            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.simplify)


(def ^:dynamic *printdebug* false) ; false


(defn nyi
  [text]
  (if (> global/verbosity 2) (println "NYI called with: " text))
  nil)

;;; simplify condition always returns a list representing a conjunction.
(defn simplify-condition [condit wrtobject])

;; In un-lvar-expression with exprn= [:field p3]
;; In un-lvar-expression with exprn= [:mode-of (TargetStates) :attacked]
;; In un-lvar-expression with exprn= [:arg-field [:field atarget] location]

(defn un-lvar-expression
  [exprn wrtobject]
  (let [evaluated (eval/evaluate-reference wrtobject exprn nil nil nil nil)
        bound-value (if (and (lvar/is-lvar? evaluated) (imag/is-bound-lvar? evaluated))
                      (imag/deref-lvar evaluated)
                      false)
        - (if (> global/verbosity 3) (println "In un-lvar-expression with exprn=" (prop/prop-readable-form exprn)
                                       "evaluates to " (prop/prop-readable-form evaluated)))
        - (if (> global/verbosity 3) (if bound-value (println "****" (lvar/.name evaluated) "=" bound-value)))
        result (if (sequential? exprn)
                 (case (first exprn)
                   :field (if bound-value [:field [:value bound-value]] exprn) ; was [:field [:value bound-value]] [:value bound-value]
                   :mode-of exprn                    ; Perhaps allow the class and the value to be lvared?+++
                   :arg-field exprn
                   exprn)
                 exprn)]
    (if (not (= exprn result)) (if (> global/verbosity 3) (println "LVAR binding applied: was: " (prop/prop-readable-form exprn)
                                                            "now:" (prop/prop-readable-form  result))))
    result))

;;; simplify-negate always returns an individual expression
(defn simplify-negate
  "maniulate the condition into conjunctive normal form and return a list of conjunctions."
  [condit wrtobject]
  ;; (println "in simplify-negate with: condit=" condit)
  (if (not (or (seq? condit) (vector? condit)))
    condit
    (case (first condit)
      ;; First handle the logical cases
      ;; NOT NOT cancels, return the simplified subexpression
      :not (let [exps (simplify-condition (second condit) wrtobject)]
             ;; Handle case where expression of not simplifies to a conjunction.
             (case (count exps)
               0 :true
               1 (first exps)
               (into [:and] exps)))
      ;; OR ~(Happy OR Sad) = ~Happy AND ~Sad
      :or (into [:and] (map (fn [sc] (simplify-negate sc wrtobject))
                            (rest condit)))
      ;; AND - ~(Happy AND Sad) = ~Happy OR ~Sad
      :and  (into [:or] (map (fn [sc] (simplify-negate sc wrtobject))
                             (rest condit)))

      ;; Handle logical inequalities
      :equal (let [exp1 (un-lvar-expression (nth condit 1) wrtobject)
                   exp2 (un-lvar-expression (nth condit 2) wrtobject)]
               [:notequal exp1 exp2])

      :notequal (let [exp1 (un-lvar-expression (nth condit 1) wrtobject)
                      exp2 (un-lvar-expression (nth condit 2) wrtobject)]
                  [:equal exp1 exp2])

      :same  (let [exp1 (un-lvar-expression (nth condit 1) wrtobject)
                   exp2 (un-lvar-expression (nth condit 2) wrtobject)]
               [:notsame exp1 exp2])

      :notsame  (let [exp1 (un-lvar-expression (nth condit 1) wrtobject)
                   exp2 (un-lvar-expression (nth condit 2) wrtobject)]
               [:same exp1 exp2])

      :implies (let [exp1 (un-lvar-expression (nth condit 1) wrtobject)
                     exp2 (simplify-negate (nth condit 2) wrtobject)]
               [:and exp1 exp2])

      ;; numerical inequalities
      :gt [:le
           (un-lvar-expression (nth condit 1) wrtobject)
           (un-lvar-expression (nth condit 2) wrtobject)]
      :lt [:ge
           (un-lvar-expression (nth condit 1) wrtobject)
           (un-lvar-expression (nth condit 2) wrtobject)]
      :ge [:lt
           (un-lvar-expression (nth condit 1) wrtobject)
           (un-lvar-expression (nth condit 2) wrtobject)]
      :le [:gt
           (un-lvar-expression (nth condit 1) wrtobject)
           (un-lvar-expression (nth condit 2) wrtobject)]

      ;; Default not is not
      [:not condit])))



;;; [:and [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]]

(defn conjunctive-list
  [condit wrtobject]
  (case (first condit)
    :and (rest condit)
    :implies (into [(first condit)] (simplify-condition [:not (second condit)] wrtobject))
    :or [condit]
    :not [condit]
    [condit]))

(defn print-condition-tersely
  [condition]
  (if (= (first condition) :thunk)
    (do
      (print "[:thunk ")
      (pprint (second condition))
      (println (.variable (nth condition 2)) "]"))
    (println condition))
  nil)

(defn pprint-condition-tersely
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
  (if (> global/verbosity 3) (println "In simplify condition with: " (prop/prop-readable-form condit)))
  (if (not (or (list? condit) (vector? condit)))
    (list condit)
    (let [result (case (first condit)
                   :thunk [(into [:thunk] (into (into [] (simplify-condition (nth condit 1) (nth condit 2))) [(nth condit 2)]))]

                   :equal [[:equal
                            (un-lvar-expression (nth condit 1) wrtobject)
                            (un-lvar-expression (nth condit 2) wrtobject)]]

                   :notequal [[:notequal
                               (un-lvar-expression (nth condit 1) wrtobject)
                               (un-lvar-expression (nth condit 2) wrtobject)]]

                   :same [[:same
                            (un-lvar-expression (nth condit 1) wrtobject)
                            (un-lvar-expression (nth condit 2) wrtobject)]]

                   :notsame [[:notsame
                              (un-lvar-expression (nth condit 1) wrtobject)
                              (un-lvar-expression (nth condit 2) wrtobject)]]

                   :gt [[:gt
                         (un-lvar-expression (nth condit 1) wrtobject)
                         (un-lvar-expression (nth condit 2) wrtobject)]]

                   :ge [[:ge
                         (un-lvar-expression (nth condit 1) wrtobject)
                         (un-lvar-expression (nth condit 2) wrtobject)]]

                   :lt [[:lt
                         (un-lvar-expression (nth condit 1) wrtobject)
                         (un-lvar-expression (nth condit 2) wrtobject)]]

                   :le [[:le
                         (un-lvar-expression (nth condit 1) wrtobject)
                         (un-lvar-expression (nth condit 2) wrtobject)]]

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
      (if (> global/verbosity 3)
        (do (println "In simplify-condition: simpres" (prop/prop-readable-form simpres))))
      simpres)))

(defn simplify-cond-top-level
  [condit wrtobject]
  (if (> global/verbosity 3) (println "In Simplify with condit=" (prop/prop-readable-form condit)
                               " wrtobject=" (.variable wrtobject)))
  (let [simplified (simplify-condition condit wrtobject)]
    #_(println "In simplify-cond-top-level" (prop/prop-readable-form condit)
             "wrt" (prop/prop-readable-form wrtobject)
             "result=" (prop/prop-readable-form condit))
    simplified))

;;; (simplify-condition '[:and [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]] nil)
;;; (simplify-condition '[:or [:same [:field handholds] [:arg object]] [:not [:equal [:arg object] [:mode-of (Foodstate) :eaten]]]] nil)
