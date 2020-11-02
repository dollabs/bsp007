;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.expressions
  "Runtime representation of expressions for evaluation"
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
            [clojure.set :as sets]
            )
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.expressions)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A variable in a Pamela expression ca refer to a number of different
;; kinds of location.  The compilation of an expression in IR form makes
;; the locations referred to explicit so that evaluation can be performed
;; expeditiously.

;; Here are the possible referents and their representation in compiled
;; form:

;; Simple references:
;; 1. Mode of an object (mode <objectref>)
;; 2. Field of an object (field <objectref> <fieldname>)
;; 3. Global variable (global <name>)
;; 4. Binding of an LVAR (lvar <lvar-name>)
;; 5. Argument of a method (arg <argname>) only within the context of a method body.

;; Complex references:
;; 1. Mode of  another object via a path of dereferencing.
;; (:modederef [...path...]) path terminates in an object.
;; 2. Field of another object via a path of dereferencing.
;; (:fieldderef [...path...]) path terminates in a field.

;; Operators that combine variables into an expression.

;; Logical operators:
;; AND (:and .n.)
;; OR  (:or .n.)
;; XOR (:xor .2.)
;; NOT (:not .1.)
;; IMPLIES (:implies .2.)

;; Numeric operators:
;; >, >=, <. <=, =, != for numeric values (.op. .o1. .02.)
;; BETWEEN (:between .lb. .1. .ub.)

;; Where:
;; .n. = N subexpressions
;; .2. = 2 subexpressions
;; .1. = 1 subexpression
;; .lb. = lower bound
;; .ub. = upper bound

;; Meta operators:

;; KNOWN (:known .1.) True of the value of the subexpression is known, false otherwise.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Constructors

;;; Logical operators

;;; Unary operators
(defn make-NOT
  "Constructor for expression conjunction"
  [part]
  [:not part])

;;; Binary operators
(defn make-XOR
  "Constructor for expression conjunction"
  [part1 part2]
  [:xor part1 part2])

(defn make-IMPLIES
  "Constructor for expression implication"
  [part1 part2]
  [:implies part1 part2])

;;; n-ary operators
(defn make-AND
  "Constructor for expression conjunction"
  [parts]
  (into [:and] parts))

(defn make-OR
  "Constructor for expression disjunction"
  [parts]
  (into [:or] parts))

;;; Numeric operators

(defn make-LESS-THAN
  "Constructor for <"
  [part1 part2]
  [:< part1 part2])

(defn make-LESS-THAN-OR-EQUAL
  "Constructor for <="
  [part1 part2]
  [:<= part1 part2])

(defn make-GREATER-THAN
  "Constructor for <"
  [part1 part2]
  [:> part1 part2])

(defn make-GREATER-THAN-OR-EQUAL
  "Constructor for <="
  [part1 part2]
  [:>= part1 part2])

;;; Function-call

(defn make-CALL
  "Constructor for function call"
  [names args]
  (vec (concat [:call (first names) (rest names)] args)))

;;; Propositions lookup
(defn make-PROPOSITIONS
  "constructor for propositions lookup"
  [condition props]
  [:lookup-propositions props condition])

;;;... to be continued
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Auxiliary functions

(defn instantiable-pclass?
  "A class that has no methods, no transitions and no fields is not instantiable."
  [pclass-spam]
  ;; First check that ir is really a pclass
  (assert (= (:type pclass-spam) :pclass) "instantiable-pclass invoked with an invalid definition.")
  (let [fields (:fields pclass-spam)
        transitions (:transitions pclass-spam)
        methods (:methods pclass-spam)]
    (or fields transitions methods)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Printers
