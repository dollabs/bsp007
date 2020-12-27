;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.lvarimpl
  "LVAR Implementation"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [clojure.data.json :as json]
            [environ.core :refer [env]]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.coredata :as global])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.lvarimpl)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lvar implementation

(defrecord LVar [name binding boundp])

(defn is-lvar?
  [thing]
  (instance? LVar thing))

(declare describe-lvar)

(defn lvar-name
  [lv]
  (if (is-lvar? lv)
    (.name lv)
    (println "ERROR: lvar-name called on a non lvar" lv)))

(defn add-lvar
  "Add an lvar to the current model."
  [lv]
  ;;  (if (not (in? (global/.lvars global/*current-model*) lv))
  (reset! (global/.lvars global/*current-model*) (cons lv @(global/.lvars global/*current-model*)))
  ) ;;)

(defn make-lvar
  [name]
  (let [lv (LVar. name (atom nil) (atom :unbound))]
    (add-lvar lv)
    lv))

(defn is-bound-lvar?
  [thing]
  (and (is-lvar? thing)
       (not (= @(.boundp thing) :unbound))))

(defn is-unbound-lvar?
  [thing]
  (and (is-lvar? thing)
       (= @(.boundp thing) :unbound)))

(defn deref-lvar
  [something]
  (if (instance? LVar something)
    (cond (is-unbound-lvar? something)
          something

          :otherwise
          (recur @(.binding something)))
    something))

(defn bind-lvar
  [lv nval]
  (if (is-unbound-lvar? lv)
    (do
      ;; (if *planbindset* (reset! *planbindset* (conj @*planbindset* lv)))
      (reset! (.boundp lv) :bound)
      (reset! (.binding lv) (deref-lvar nval)))
    (let [boundto (deref-lvar lv)]
      (if (instance? LVar boundto)
        (recur boundto nval)
        (= boundto (deref-lvar nval))))))

(defn unbind-lvar
  [lv]
  (reset! (.boundp lv) :unbound)
  (reset! (.binding lv) nil))

;;; (def x (make-lvar "x"))
;;; x
;;; (start-plan-bind-set)
;;; *planbindset*
;;; (bind-lvar x 42)
;;; x
;;; *planbindset*
;;; (stop-plan-bind-set)
;;; x
;;; *planbindset*

(defn lvar-string
  [lv]
  (let [name (.name lv)]
    (if (is-bound-lvar? lv)
      (format "?%s=%s" name (str (deref-lvar lv)))
      (format "?%s" name))))

(defn describe-lvar
  [lv]
  (.write *out* (format "<LVAR name=%s%s%s>%n"
                        (.name lv)
                        (if (is-unbound-lvar? lv) "" " value=")
                        (if (is-unbound-lvar? lv) "" (deref-lvar lv)))))
