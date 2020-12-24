;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.prop
  "Pamela Readable Object Printer"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [environ.core :refer [env]]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.coredata :as global]
            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.prop)

(def ^:dynamic lvar-string-impl lvar/lvar-string) ;+++ bind this to imag/lvar-string when in bsp

(defn prop-readable-form
  "Convert the object into a clojure form that can be printed or pprinted"
  [object]
  (cond
    (lvar/is-lvar? object)
    (lvar-string-impl object)

    (global/RTobject? object)
    (str "$" (global/RTobject-variable object))

    (global/MethodQuery? object)
    (str "q{" (global/.pclass object) "|"
         (prop-readable-form (global/.methodsig object)) "|"
         (prop-readable-form (global/.rootobject object)) "|"
         (prop-readable-form (global/.rto object)) "}")

    (instance? clojure.lang.Atom object)
    (str "@" (prop-readable-form @object))

    (list? object)
    (into () (map prop-readable-form object))

    (vector? object)
    (into [] (map prop-readable-form object))

    (sequential? object)
    (into [] (map prop-readable-form object))

    (map? object)
    (case (:type object)
      :method-fn
      (str "m{" (prop-readable-form (:method-ref object))
           ":"  (prop-readable-form (:args object)) "}")

      :field-ref
      (apply str (map (fn[name] (str "." name)) (:names object)))

      (if (:mname object)
        (str "m{" (:mname object) "}")
        (into {} (map (fn [[k v]] [k (prop-readable-form v)]) object))))

    :otherwise
    (do ;(println "**** WHAT IS THIS? " object)
        object)))

(defn prop-print
  [object]
  (println (prop-readable-form object)))


(defn prop-pprint
  [object]
  (pprint (prop-readable-form object)))
