;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.coredata
  "Runtime Model"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [environ.core :refer [env]]
            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.coredata)

(defrecord RuntimeModel [lvars
                         objects
                         plantmap
                         pclasses
                         pre-and-post-conditions
                         invertedinfluencehashtable
                         rootclass])

(defrecord RTobject [variable type fields id])
(defn prs [x] (with-out-str (prn x)))

(defn RTobject?
  [x]
  (instance? RTobject x))

(defn RTobject-type
  [rto]
  (.type rto))

(defn RTobject-variable
  [rto]
  (.variable rto))

(defn RTobject-id
  [rto]
  (.id rto))

(defn RTobject-fields
  [rto]
  (.fields rto))

(defn make-object
  [var typ fields id]
  (RTobject. var typ (atom fields) id))

;;; A model is a map with a list of instantiated objects that constitute the model
;;; and a list of structural lvars.
;;; Each instantiated object is a map with entries for the object type,
;;; the fields of the object, and a variable-name that represents the
;;; belief state of the mode.

(def ^:dynamic *current-model* (RuntimeModel. (atom nil) ;lvars
                                              (atom nil) ;objects
                                              (atom {})  ;plantmap
                                              (atom {})  ;pclasses
                                              (atom {})  ;pre-and-post-conditions
                                              (atom {})  ;invertedinfluencehashtable
                                              (atom nil))) ;rootclass

(def ^:dynamic verbosity 0) ; 0

(defn set-verbosity
  [n]
  (def ^:dynamic verbosity n))

(defn get-root-objects
  "Returns the root object."
  []
  (let [objects @(.plantmap *current-model*)]
    (remove nil? (map (fn [[id rtobj]]
                        (if (= id "root") [id rtobj] nil))
                      objects))))

(defn root-object
  []
  (second (first (get-root-objects))))

(defn add-object
  "Add an object to the current model."
  [object]
  ;;  (if (not (in? (.objects *current-model*) object))
  (reset! (.objects *current-model*) (cons object @(.objects *current-model*)))
  ) ;;)

(defn remove-object
  "Remove an object from the current model."
  [object]
  (reset! (.objects *current-model*) (remove #{object} @(.objects *current-model*))))

(defn add-pclasses
  "Add an pclasses from a loaded model file."
  [pcs]
  (if (> verbosity 1)
    (do (println "adding spam:\n")
        (pprint pcs)))
  (reset! (.pclasses *current-model*) pcs)) ;+++ unfinished, thsi needs to merge with whats already there

(defn add-preandpost
  "Add a preandpost condition vector from a loaded model file."
  [ppcs]
  (if (> verbosity 2)
    (do
      (if (> verbosity 1) (println "adding pre-and-post-conditions:\n"))
      (pprint ppcs)))
  (reset! (.pre-and-post-conditions *current-model*) ppcs))

(defn add-plant
  "Add an object to the current model."
  [plantid instance]
  ;;  (if (not (in? (.objects *current-model*) object))
  (reset! (.plantmap *current-model*) (into @(.plantmap *current-model*) {plantid instance}))
  ) ;;)

(defn get-object-from-id
  "Lookup the instantiated object given an ID."
  [id]
  (let [plantmap @(.plantmap *current-model*)
        object (get plantmap (name id))]
    object))

(defrecord MethodQuery [pclass methodsig rootobject rto])

(defn MethodQuery? [obj] (instance? MethodQuery obj))

(defn make-method-query
  [pclass methodsig rootobject rto]
  (MethodQuery. pclass methodsig rootobject rto))
