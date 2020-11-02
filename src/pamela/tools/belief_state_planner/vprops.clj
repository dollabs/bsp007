;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.vprops
  "Virtual Propositions"
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
            [pamela.tools.belief-state-planner.simplify :as simp]
            [pamela.tools.belief-state-planner.buildir :as bir]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.evaluation :as eval]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.prop :as prop]
            [pamela.tools.belief-state-planner.imagine :as imag]

            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.vprops)

(defn nyi ;+++ nyi should be globally defined.
  [text]
  (if (> global/verbosity 2) (println "NYI called with: " text))
  nil)

(def virtual-propositions {})

(defn add-virtual-proposition
  "A virtual proposition computes propositions that are not explicitely represented."
  [prop handler]
  (def virtual-propositions (into virtual-propositions {prop handler}))
  (map first virtual-propositions))

(defn remove-virtual-proposition
  "A virtual proposition computes propositions that are not explicitely represented."
  [prop]
  (def virtual-propositions (into {} (remove #(= (first %) prop) virtual-propositions)))
  (map first virtual-propositions))

;;; (def-virtual-proposition :foo [arglist] body)
(defmacro def-virtual-proposition
  "Define a virtual proposition handler and install it- cf add-virtual-proposition."
  [vpname argvec & body]
  (let [handler-f-name (symbol (str (subs (str vpname)
                                          (if (keyword? vpname) 1 0))
                                    "-vp-handler"))
        handler `(def ~handler-f-name
                   (fn ~argvec
                     "generated from def-virtual-proposition"
                     ~@body))]
    `(do ~handler (add-virtual-proposition ~(if (keyword? vpname) vpname `'~vpname) ~handler-f-name))))

;;; (pprint (macroexpand '(def-virtual-proposition :bar [prop a1 a2] (println prop a1 a2))))

;;; (add-virtual-proposition :foo 42)
;;; (def-virtual-proposition :bar [prop a1 a2] (println prop a1 a2))
;;; (:bar virtual-propositions)
;;; (remove-virtual-proposition :foo)

(defn virtual-proposition?
  [prop]
  (contains? virtual-propositions prop))

;;; (virtual-proposition? :bar)

(defn invoke-virtual-proposition
  [prop arg1 arg2]
  ((get virtual-propositions prop) prop arg1 arg2))

;;; (invoke-virtual-proposition :bar 1 2)

;;; Squares a given number

(def-virtual-proposition :squared
  [prop arg1 arg2]
  (let [result
        (cond
          (and (number? arg1) (number? arg2))
          (if (= (float (* arg1 arg1)) (float arg2))
            [{:ptype prop, :subject (float arg1) :object (float arg2) :type :binary}]
            [])

          (and (number? arg1) (nil? arg2))
          [{:ptype prop, :subject (float arg1) :object (float (* arg1 arg1)) :type :binary}]

          (and (nil? arg1) (number? arg2))
          [{:ptype prop, :subject (Math/sqrt arg2) :object (float arg2) :type :binary}]

          :otherwise
          (do (println "Unhandled case in :squared virtual-proposition [" prop arg1 arg2 "]")
              []))]
    (println "vprop" prop arg1 arg2 "=" result)
    result))

;;; fin
