;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.planexporter
  "Evaluation"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [environ.core :refer [env]]
            [pamela.cli :as pcli]
            [pamela.tpn :as tpn]
            [pamela.unparser :as pup]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.prop :as prop]
            [pamela.tools.belief-state-planner.imagine :as imag]

            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.planexporter)

(defn translate-plan
  [plans]
  (println "translating plans: " plans)
  (map (fn [a-plan]
         (map (fn [step]
                (into [:call (nth step 0)] ; Function name
                      (rest step)))
              a-plan))
       plans))

(defn translate-method-name
  [amethod]
  (let [name (get amethod :names)]
    (if (not name)
      (irx/error "In translate-method-name: Method name not found in; " amethod)
      (last name))))                    ; +++ can the multiply dotted case exist here?

(defn translate-arg
  [anarg]
  (if (and (vector? anarg) (not (empty? anarg)))
    (case (first anarg)
      :field
      (cond
        (vector? (second anarg))
        (if (= (first (second anarg)) :value)
          (second (second anarg)))

        :otherwise (second anarg))

      :arg-field
      'wtf                          ;+++ fixme

      :value
      (second anarg)

      (do
        (println "Unhandled argument type found in translate-arg: " anarg)
        anarg))
    anarg))

(defn value-field-arg
  [anarg]
  (and (= (first anarg) :field)
       (sequential? (second anarg))
       (= (first (second anarg)) :value)))

(defn replace-first-arg
  [meth nuarg]
  (conj meth { :args [nuarg] }))

(defn clean-solutions
  [solutions]
  (map (fn [asoln]
         (let [firstargs
               (concat (map (fn [astep]
                              (let [[meth pred] astep
                                    arg1 (first (get meth :args))]
                                arg1))
                            (rest asoln))
                       (list nil))
               cleaned
               (map (fn [astep farg]
                      (let [[meth pred] astep
                            arg1 (first (get meth :args))]
                        (if (value-field-arg arg1)
                          [(replace-first-arg meth farg) pred]
                          astep)))
                    asoln firstargs)]
           cleaned))
       solutions))

(defn compile-plan
  [solutions]
  (let [cleaned-solutions (clean-solutions solutions)
        compiled-result
        (map (fn [asoln]
               (map (fn [astep]
                      (let [item (first astep)
                            method (get item :method-ref)
                            method-name (translate-method-name method)
                            args (get item :args)
                            args-name (map translate-arg args)]
                        (into [method-name] args-name)))
                    asoln))
             cleaned-solutions)]
    ;; Fix this in the DMCP. +++pr
    (println "solutions = " solutions "cleaned-solutions = " cleaned-solutions "compiled-result = " compiled-result)
    (doall compiled-result)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Emitters for ir

(defn emit-pclass
  [pclass-name args method-list]
  {pclass-name
   {:args args,
    :methods method-list
    :type :pclass}})

(defn emit-pmethod ; body is a list
  [pmethod-name args body]
  [pmethod-name
   (list {:args args,
          :body body})])

(defn emit-sequence ; body is a list
  [body]
  {:type :sequence
   :body body})

(defn emit-parallel ; body is a list
  [body]
  {:type :parallel
   :body body})

(defn emit-choose ; body is a list
  [body]
  {:type :choose,
   :body body})

(defn emit-choice ; body is a list
  [body]
  {:type :choice,
   :body body})

(defn emit-args
  [args]
  (if args (map (fn [arg] {:type :state-variable, :name arg}) args) []))

(defn emit-call
  [name args]
  ;;(println "In emit-call args=" args)
  {:type :method-fn,
   :method-ref
   {:type :symbol-ref, :names [name]},
   :args (emit-args args)})

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Emitters for Pamela


(defn emit-pclass-pamela
  [pclass-name args method-list]
  (list 'defpclass
        pclass-name
        (or args [])
        :methods (vec method-list)))

(defn emit-pmethod-pamela ; body is a list
  [pmethod-name args body]
  (println "In emit-pmethod-pamela with pmethod-name=" pmethod-name "args=" args "body=" body)
  (concat (list 'defpmethod pmethod-name (vec (or args [])))
          (if (or (= body '((parallel)))
                  (= body '((sequential)))
                  (= body '((sequential (parallel))))
                  (= body '((parallel (sequential)))))
            '()
            body)))

(defn emit-sequence-pamela ; body is a list
  [body]
  (cons 'sequence body))

(defn emit-parallel-pamela ; body is a list
  [body]
  (cons 'parallel body))

(defn emit-choose-pamela ; body is a list
  [body]
  (cons 'choose body))

(defn emit-choice-pamela ; body is a list
  [body]
  (cons 'choice body))

(defn emit-args-pamela
  [args]
  (or (into [] (map (fn [arg] arg) args)) []))

(defn emit-call-pamela
  [name args]
  (cons name (emit-args-pamela args)))

(defn convert-symbolic-tpn-to-pamela
  [symbolic]
  (println "In convert-symbolic-tpn-to-pamela with symbolic=" symbolic)
  (if (not (sequential? symbolic))
    (do (println "Unexpected value: " symbolic " in convert-symbolic-tpn-to-pamela")
        symbolic)
    (case (first symbolic)
      :pclass
      (emit-pclass-pamela (second symbolic) ; name
                   (or (nth symbolic 2) []) ; args
                   (vec (doall (map (fn [x]
                                 (convert-symbolic-tpn-to-pamela x))
                               (nth symbolic 3)))))

      :pmethod
      (emit-pmethod-pamela (second symbolic) ; method name
                    (or (nth symbolic 2) []) ; arglist (or nil)
                    (map convert-symbolic-tpn-to-pamela (nth symbolic 3)))

      :parallel
      (emit-parallel-pamela (map convert-symbolic-tpn-to-pamela (rest symbolic)))

      :sequence
      (emit-sequence-pamela (map convert-symbolic-tpn-to-pamela (rest symbolic)))

      :call
      (emit-call-pamela (second symbolic)
                 (map (fn [arg] arg)
                      (nth symbolic 2)))
      :choice
      (emit-choose-pamela
       (map (fn [achoice]
              (emit-choice-pamela (list (convert-symbolic-tpn-to-pamela achoice))))
            (rest symbolic)))

      symbolic))) ;; unhandled cases are dumped in unconverted

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Generating a symbolic form from a plan

(defn compile-call
  [acall]
  (if (get #{"lateral" "start" "down"} (first acall)) ;+++ remove this obsolete logic
    (let [direction (first acall)
          objname (second acall)
          classname (if (>= (count acall) 4) (nth acall 3) objname)]
      (if (not (= direction "start"))
        [:call (if (= direction "lateral") 'move-lateral 'move-down)
         (list classname)]))
    (do
      (println "acall=" acall)
      acall)))

(defn encode-as-tpn
  [sequence paths]
  ;;(println "seq=" sequence "remain=" paths)
  (if (empty? (first paths))
    sequence
    (if (every? #(= (second (first (first paths))) (second (first  %))) paths)
      (let [call (compile-call (first (first paths)))]
        (encode-as-tpn (if (not (empty? call))
                         (into sequence [call])
                         sequence)
                       (remove empty? (map rest paths))))
      (into sequence
            (let [divergeset (into #{} (map (fn [x] (second (first x))) paths))
                  ;; - (println "divergeset=" divergeset)
                  threads (map (fn [target]
                                 (remove nil?
                                         (map (fn [path]
                                                (if (= (second (first path)) target) path))
                                              paths)))
                               divergeset)]
              ;;(println "threads=" threads)
              [(into [:choice]
                     (map (fn [x]
                            (if (> (count (first x)) 1)
                              (into  [:sequence] (encode-as-tpn [] x))
                              (first (encode-as-tpn [] x))))
                          threads))])))))

;;; +++ obsolete, remove me
(defn reverse-labeling-of-plans
  [aplan]
  (map (fn [aseq]
         (let [labels (into [] (map #(first %) aseq))]
           (map (fn [act nulab]
                  (cons nulab (rest act)))
                aseq (take (count aseq) labels))))
       aplan))

(defn make-contingent-tpn-from-plan
  [plan]
  (let [aplan (reverse-labeling-of-plans plan)]
    (if (= (count aplan) 1)
      (encode-as-tpn [:sequence] aplan)
      ;; First divide the major parallel plans based on target
      (let [targetset (into #{} (map last aplan))
            ;; - (println "target set is: " targetset)
            threads (map (fn [target]
                           (remove nil?
                                   (map (fn [path]
                                          (if (= (last path) target) path))
                                        aplan)))
                         targetset)]
        (if (not (empty? threads))
          (into [:choice] #(into [:sequence] (encode-as-tpn [] %)) threads)
          nil)))))


(defn make-pclass-for-top
  [name]
  (list 'defpclass 'Top [] :fields {'ta (list name)}))

;;; pclass-name is the class name of the solution
;;; pcargs is any arguments that thepclass expects
;;; pmethod-name is the solution method name
;;; args is the arglist for the pmethod
;;; plan is the generated plan
;;; mmap is the list of pmethods referred to in the plan and the number of arguments that they take

(defn make-pclass-for-tpn
  [pclass-name pcargs pmethod-name args plan mmap]
  (let [pmethods
        (map (fn [[mname margs]]
               [:pmethod mname (into [] (map (fn [n] (symbol (str "arg" (str n)))) (range 1 (+ margs 1)))) ()])
             mmap)]
    [:pclass pclass-name pcargs
     (conj pmethods
           [:pmethod pmethod-name args
            (let [pap (make-contingent-tpn-from-plan plan)] (if pap (list pap) ()))])]))

(defn convert-plan-to-pamela
  [plan rpclass rmeth]
  (let [mmap (into {} (map (fn [acall] { (second acall) (- (count (rest acall)) 1) }) plan))]
    (list
     (make-pclass-for-top rpclass)
     (convert-symbolic-tpn-to-pamela
      (make-pclass-for-tpn rpclass nil rmeth nil plan mmap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn create-tpn-json-file-from-pamela [tpn-in-pamela]
  ;; Pamela should someday be extended so we didn't have to write and read these temporary files
  (let [pamela-file (java.io.File/createTempFile "pamela-source" ".pamela")
        tpn-json-file (java.io.File/createTempFile "pamela-json" ".tpn.json")
        [top-form attacker-form] tpn-in-pamela]
    (with-open [ostrm (clojure.java.io/writer pamela-file)]
      ;; Take advantage of the fact that Pamela uses the same basic syntax as Clojure
      (pprint top-form ostrm)
      (pprint attacker-form ostrm))
    ;;For testing only
    ;; (reset! tpn/my-count (rand-int 10000))
    (pcli/tpn {:input [pamela-file]
               :output tpn-json-file
               :file-format "json"
               :construct-tpn "Top:ta:main"})
    tpn-json-file))


(defn assemble-solutions
  [solutions rclass rmeth]
  (println "In assemble-solutions with rclass=" rclass "rmeth=" rmeth "solutions=" solutions)
  (let [plans (into [] (translate-plan solutions))
        jplans (json/write-str (into [] solutions))
        tpn-net-pamela (convert-plan-to-pamela plans rclass rmeth)
        _ (pprint tpn-net-pamela)
        tpn-file (create-tpn-json-file-from-pamela tpn-net-pamela)]
    (pprint tpn-file)
    jplans))
