;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.conapsp
  "Step distance in planning space for monte-carlo priors"
  (:require [clojure.string :as string]
            ;;[clojure.core :refer [inst-ms]]
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
            [pamela.tools.belief-state-planner.vprops :as vp]

            [pamela.cli :as pcli]
            [pamela.unparser :as pup]
            )
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.conapsp)

(def INF 9999.0)

(defn apsp
  [cmap]
  ;; Initialize the working array
  (let [num-vertices (count cmap)
        dist (make-array Float/TYPE num-vertices num-vertices)]
    ;; Load working array
    (dotimes [i num-vertices]
      (dotimes [j num-vertices]
        (aset-float dist i j (nth (nth cmap i) j))))
    ;; Floyd-Warshall
    (dotimes [k num-vertices]
      (dotimes [i num-vertices]
        (dotimes [j num-vertices]
          (if (< (+ (aget dist i k) (aget dist k j)) (aget dist i j))
            (aset-float dist i j (+ (aget dist i k) (aget dist k j)))))))
    ;; Unload result
    (map (fn [i]
          (map (fn [j] (aget dist i j)) (range num-vertices)))
         (range num-vertices))))

(defn printGraph
  "Prints out an apsp distance map. prints out decimal part to save printout space."
  [cmap]
  (let [num-vertices (count cmap)]
    (dotimes [i num-vertices]
      (dotimes [j num-vertices]
        (if (= (nth (nth cmap i) j) INF)
          (print " INF ")
          (print (format "%3d" (int (nth (nth cmap i) j))) " ")))
      (println))))

;;; Test for apsp
(defn apsp-test
  []
  (let [graph [[0.00  5.00  INF  10.00]
               [INF   0.00  3.00  INF]
               [INF   INF   0.00  1.00]
               [INF   INF   INF   0.00]]
        correctSolution [[0.00  5.00  8.00  9.00]
                         [INF   0.00  3.00  4.00]
                         [INF   INF   0.00  1.00]
                         [INF   INF   INF  0.00]]
        solution (apsp graph)]
    (if (not (= solution correctSolution))
      (do
        (println "Input graph:")
        (printGraph graph)
        (println "Output solution:")
        (printGraph solution)
        :failed))))

(defn shortest-distance
  [apsp x y]
  (let [{namemap :namemap
         pnames :pnames
         cmap :cmap
         portal-connects-map :pcm
         apsp-graph :apsp} apsp
        indexx (.indexOf pnames x)
        indexy (.indexOf pnames y)]
    (if (and (>= indexx 0) (>= indexy 0))
      (let [dist (nth (nth apsp-graph indexx) indexy)]
        dist)
      (do
        (if (< indexx 0) (println "x not found in pnames" x pnames))
        (if (< indexy 0) (println "y not found in pnames" y pnames))
        nil))))

(defn apsp-distances
  [apsp x]
  (let [{namemap :namemap
         onames :onames
         cmap :cmap
         portal-connects-map :pcm
         apsp-graph :apsp} apsp
        numnames (count onames)
        indexx (.indexOf onames x)]
    (if (>= indexx 0)
      (into {} (map (fn [indexy]
                      {indexy (nth (nth apsp-graph indexx) (.indexOf onames indexy))})
                    onames))
      (do
        (if (< indexx 0) (println "x not found in onames" x onames))
        nil))))

(defn apsp-reverse-distances
  [apsp ys]
  (println "apsp=" apsp "ys=" ys)
  (let [{namemap :namemap
         onames :onames
         cmap :cmap
         portal-connects-map :pcm
         apsp-graph :apsp} apsp
        numnames (count onames)]
    (if (> (count ys) 0)
      (into {} (map (fn [indexx]
                      (let [cands (into []
                                        (map
                                         (fn [indexy]
                                           ;;(println "onames=" onames "x="
                                                    indexx "("  (.indexOf onames indexx) ") y="
                                                    indexy "("  (.indexOf onames indexy) ")")
                                           [indexx (nth (nth apsp-graph (.indexOf onames indexx))
                                                        (.indexOf onames indexy))])
                                         ys))]
                        ;;(println "cands=" cands)
                        (apply min-key second cands)))
                    onames))
      (do
        (println "ys empty" ys)
        nil))))

;;; (apsp-test)

(defn compute-connectivity-map-from-objects
  [[objects distance-function filterfn]]
  "Computes a map from portal objects to a set of spaces names that they connect."
  (let [cmap (into {}
                   (map (fn [anobject]
                          (let [oname  (global/RTobject-variable anobject)
                                cprops (bs/find-binary-propositions-matching
                                        #{oname} nil #{:connects-with} nil nil nil)
                                conto (into #{} (remove nil? (map (fn [o]
                                                                    (if (filterfn o) (:object o)))
                                                                  cprops)))]
                            {anobject conto}))
                        objects))]
    ;; (println "Here is the connectivity map:")
    ;; (pprint cmap)
    (def ^:dynamic *cached-cmap* cmap)
    [cmap distance-function]))

(defn compute-distances-between-objects
  [[cmap distance-function]]
  ;; For every object, compute the distance from that object to every other object with
  ;; a direct connection
  (let [object-connects-map
        (into {}
              (map (fn [[anobject cset]]
                     (let [connections
                           (into {}
                                 (remove nil?
                                         (map (fn [[anobject2 cset2]]
                                                (let [shared (clojure.set/intersection cset cset2)]
                                                  (if (not (empty? shared))
                                                    {(global/RTobject-variable anobject2)
                                                     (distance-function anobject anobject2)}))) ; distance-between-objects
                                              cmap)))]
                       (if (not (empty? connections))
                         {(global/RTobject-variable anobject) connections})))
                   cmap))]
    ;; (println "object-connects-map:")
    ;; (pprint object-connects-map)
    [cmap object-connects-map]))

(defn get-object-vname
  [artobj]
  ;;(println "get-object-vname:" artobj)
  (if artobj
    (global/RTobject-variable artobj)
    "Unknown"))

(defn compute-connectivity-matrix
  [[cmap object-connects-map]]
  ;; Create a connectivity matrix as input to apsp
  (let [onames (map first object-connects-map)
        vnames (map (fn [oome] (get-object-vname (first oome))) cmap)
        namemap (into {} (map (fn [oname vname] {oname vname}) onames vnames))
        ;;_ (println "name map is:" namemap)
        cmap4apsp (into []
                        (map
                         (fn [aFromOname]
                           (let [fromMap (get object-connects-map aFromOname)]
                             (into []
                                   (map
                                    (fn [aToOname]
                                      (get fromMap aToOname INF))
                                    onames))))
                         onames))]
    ;; (println "onames=" onames "cmap4apsp:")
    ;; (printGraph cmap4apsp)
    [namemap onames cmap object-connects-map cmap4apsp]))

(defn compute-apsp
  [[namemap onames cmap object-connects-map cmap4apsp]]
  (let [apsp-graph (apsp cmap4apsp)]
    (println "APSP graph:")
    (printGraph apsp-graph)
    {:namemap namemap
     :onames onames
     :cmap cmap
     :pcm object-connects-map
     :apsp apsp-graph}))


(defn compute-connectivity-map
  [objects distance-function filterfn]
  (-> [objects distance-function filterfn]
      compute-connectivity-map-from-objects
      compute-distances-between-objects
      compute-connectivity-matrix
      compute-apsp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
