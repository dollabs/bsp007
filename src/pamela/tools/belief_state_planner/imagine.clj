;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.imagine
  "Imagined sate of the world after planned actions"
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
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.expressions :as dxp]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.prop :as prop]

            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.imagine)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Monitors

(def ^:dynamic *monitors* (atom #{}))
(def ^:dynamic *monitor-on* (atom true))

(defn set-monitor-on
  [trueorfalse]
  (reset! *monitor-on* trueorfalse))

(defn monitor-field
  [obj field]
  (reset! *monitors* (clojure.set/union #{[obj field]} (deref *monitors*))))

(defn monitoring-field?
  [obj field]
  (not (empty? (clojure.set/intersection (deref *monitors*) #{[obj field]}))))

(defn check-monitor
  [obj field value]
  (if (and (deref *monitor-on*) (> global/verbosity 3) (monitoring-field? obj field))
    (println "Establishing " (format "%s.%s=%s" (name obj) (name field) (str value)))))

(defn check-monitor-update
  [kobj kfield value obj]
  (let [val (deref obj)]
    (if (and  (deref *monitor-on*) (> global/verbosity 3) (monitoring-field? kobj kfield))
      (if (or (not (= value val)) (> global/verbosity 4))
        (println "Updating " (format "%s.%s=%s" (name kobj) (name kfield) value))))))

(defn get-monitors
  []
  (let [mons (vec (doall (map (fn [memb] memb) (deref *monitors*))))]
    mons))

(defn print-monitors
  []
  (doseq [[obj field] (get-monitors)] (println (format "Monitoring %s.%s" (name obj) (name field)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Object references

(def ^:dynamic *imagined-objects* {})

(defmacro with-no-imagination
  [& body]
  `(binding [*imagined-objects* {}]
     ~@body))

(def field-lock (Object.))

(def ^:dynamic *planbindset* nil)

(defmacro with-no-lvar-plan-bindings
  [& body]
  `(binding [*planbindset* nil]
     ~@body))


(defn reset-imagination
  "Forget imagined state to begin a new episode."
  []
  (set! *imagined-objects* {}))

(defn print-field-values
  []
  (pprint *imagined-objects*))

;;; Returning NIl means that it was not found and hence the world-state value should be used.
(defn get-field-value
  [obj field]
  ;; (println "Looking for " obj "." field)
  (locking field-lock
    (let [source (get *imagined-objects* (keyword obj))]
      (if source
        (let [value (get (deref source) (keyword field))]
          (if value (deref value)))))))

(defn get-mode
  [obj]
  (get-field-value obj :mode))

(defn update-field-value
  [obj field value]
  (locking field-lock
    (let [kobj (keyword obj)
          kfield (keyword field)
          known-source (get *imagined-objects* kobj)] ; nil or an atom
      ;; (println (format "Setting %s.%s=%s" (name kobj) (name kfield) (str value)))
      (if known-source
        (let [known-field (get (deref known-source) kfield)] ; The source is known, but what about the field?
          (if known-field
            (do
              (check-monitor-update kobj kfield value known-field)
              (reset! known-field value))                ; Source and field known so just set the value.
            (do
              (check-monitor kobj kfield value)
              (reset! known-source (merge (deref known-source) {kfield (atom value) }))))) ; add new field/value
        (do ; If the source is not known, the object the field and its value must be set
          (check-monitor kobj kfield value)
          (set! *imagined-objects* (merge  *imagined-objects* { kobj (atom { kfield (atom value) }) })))))))

(defn imagine-changed-field-value
  "Can be given the variable name of the object or the runtime object itself"
  [obj field value]
  (if (> global/verbosity 0)
    (println "*** imagine-changed-field-value obj=" (prop/prop-readable-form obj) "field=" field "value=" value))
  (if (global/RTobject? obj)
    (update-field-value (global/RTobject-variable obj) field value)
    (update-field-value obj field value)))

(defn imagine-changed-object-mode
  "Imagine a mode for the object"
  [obj value probability]
  ;; +++ not using probability yet -- fixme +++
  (imagine-changed-field-value obj :mode value))

(defn imagine-lvar-binding
  "Imagine an LVAR binding.  nil couns as unbound."
  [lvar value]
  (if (and (lvar/is-lvar? lvar)
           (lvar/is-unbound-lvar? lvar))
    (imagine-changed-field-value (.name lvar) :lvar value)
    (= (lvar/deref-lvar value)
       (get-field-value (.name lvar) :lvar))))

(defn print-imagination
  "Print out everything that is in the imagination"
  []
  (println "Contents of imagination:")
  (doseq [[name value] *imagined-objects*]
    (doseq [[field val] @value]
      (println name "." field "=" @val))))

(defn is-bound-lvar?
  [thing]
  (or
   (get-field-value (.name thing) :lvar)
   (lvar/is-bound-lvar? thing)))

(defn is-unbound-lvar?
  [thing]
  (and
   (not (get-field-value (.name thing) :lvar))
   (lvar/is-unbound-lvar? thing)))

(defn deref-lvar
  [something]
    (if (lvar/is-lvar? something)
      (let [imagined (get-field-value (lvar/lvar-name something) :lvar)]
        (cond (not imagined)
              (lvar/deref-lvar something)

              imagined
              (recur imagined)))
      something))

(defn bind-lvar
  [lv nval]
  (if (is-unbound-lvar? lv)
    (do
      (if *planbindset* (reset! *planbindset* (conj @*planbindset* lv)))
      (imagine-lvar-binding lv (deref-lvar nval)))
    (let [boundto (deref-lvar lv)]
      (if (lvar/is-lvar? boundto)
        (recur boundto nval)
        (= boundto (deref-lvar nval))))))

(defn unbind-lvar
  [lv]
  (let [imagined (get-field-value (lvar/lvar-name lv) :lvar)]
    (if imagined
      (imagine-lvar-binding lv nil)
      (do (println "*** ERROR shouldn't get here ***") (lvar/unbind-lvar lv)))))

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

;;; Start tracking LV bind operations

(defn unbind-planbind-set
  []
  (if *planbindset*
    (do
      (doseq [lvar @*planbindset*]
        (if (> global/verbosity 1) (println "Unbinding LVAR " (.name lvar)))
        (unbind-lvar lvar)))))

(defn start-plan-bind-set
  []
  (if (> global/verbosity 1) (println "Starting to collect LVAR bindings"))
  (if (not (= *planbindset* nil)) (unbind-planbind-set))
  (set! *planbindset* (atom #{})))

(defn stop-plan-bind-set
  []
  (if (> global/verbosity 1) (println "Stopping collecting LVAR bindings"))
  (unbind-planbind-set)
  (set! *planbindset* nil))
