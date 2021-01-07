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
            [pamela.tools.belief-state-planner.buildir :as bir]
            [pamela.tools.belief-state-planner.dmcgpcore :as core]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.prop :as prop]
            [pamela.tools.belief-state-planner.imagine :as imag]

            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.planexporter)

(defn translate-plan
  [plans]
  ;; (println "translating plans: " plans)
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
    ;; (println "solutions = " solutions "cleaned-solutions = " cleaned-solutions "compiled-result = " compiled-result)
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
  [pclass-name args field-list method-list]
  #_(println "In emit-pclass-pamela with pclass-name=" pclass-name
           "args=" args "field-list=" field-list "method-list=" method-list)
  `(~'defpclass
        ~pclass-name
        ~(or args [])
        ~@(if (not (empty? field-list)) (list :fields (into {} field-list)))
        ~@(if (not (empty? method-list)) (list :methods (into [] method-list)))))

(defn emit-pmethod-pamela ; body is a list
  [pmethod-name args body]
  #_(println "In emit-pmethod-pamela with pmethod-name=" pmethod-name "args=" args "body=" body)
  (concat (list 'defpmethod pmethod-name (vec (or args [])))
          (if (or (= body '((parallel)))
                  (= body '((sequence)))
                  (= body '((sequence (parallel))))
                  (= body '((parallel (sequence)))))
            '()
            body)))

(defn emit-field-pamela
  [field-name field-value]
  #_(println "In emit-field-pamela with field-name=" field-name "field-value=" field-value)
  [field-name field-value])

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
  #_(println "In convert-symbolic-tpn-to-pamela with symbolic=" symbolic)
  (if (not (sequential? symbolic))
    (do ;(println "Unexpected value: " symbolic " in convert-symbolic-tpn-to-pamela")
        symbolic)
    (case (first symbolic)
      :pclass
      (emit-pclass-pamela (nth symbolic 1)  ; name
                   (or (nth symbolic 2) []) ; args
                   (vec (doall (map (fn [x] ; fields
                                 (convert-symbolic-tpn-to-pamela x))
                                    (nth symbolic 3))))
                   (vec (doall (map (fn [x] ; methods
                                 (convert-symbolic-tpn-to-pamela x))
                               (nth symbolic 4)))))

      :field
      (emit-field-pamela (nth symbolic 1) ; field name
                    (convert-symbolic-tpn-to-pamela (nth symbolic 2))) ; value

      :pmethod
      (emit-pmethod-pamela (second symbolic) ; method name
                    (or (nth symbolic 2) []) ; arglist (or nil)
                    (map convert-symbolic-tpn-to-pamela (nth symbolic 3))) ; body

      :parallel
      (emit-parallel-pamela (map convert-symbolic-tpn-to-pamela (rest symbolic)))

      :sequence
      (emit-sequence-pamela (map convert-symbolic-tpn-to-pamela (rest symbolic)))

      :call
      (emit-call-pamela (second symbolic) (rest (rest symbolic)))

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
      #_(println "acall=" acall)
      acall)))

(defn encode-as-tpn
  [sequence paths]
  ;; (println "seq=" sequence "remain=" paths)
  (if (empty? (first paths))
    sequence
    (if (every? #(= (first (first paths)) (first  %)) paths) ; (second) (second)
      (let [call (compile-call (first (first paths)))]
        (encode-as-tpn (if (not (empty? call))
                         (into sequence [call])
                         sequence)
                       (remove empty? (map rest paths))))
      (into sequence
            (let [divergeset (into #{} (map (fn [x]  (first x))) paths) ;(second)
                  ;; _ (println "divergeset=" divergeset)
                  threads (map (fn [target]
                                 (remove nil?
                                         (map (fn [path]
                                                (if (= (first path) target) path)) ; (second)
                                              paths)))
                               divergeset)]
              ;; (println "threads=" threads)
              [(into [:choice]
                     (map (fn [x]
                            (if (> (count (first x)) 1)
                              (into  [:sequence] (encode-as-tpn [] x))
                              (first (encode-as-tpn [] x))))
                          threads))])))))

;;; +++ obsolete, remove me (carefully)
(defn reverse-labeling-of-plans
  [aplan]
  (map (fn [aseq]
         (let [labels (into [] (map #(first %) aseq))]
           (map (fn [act nulab]
                  (cons nulab (rest act)))
                aseq (take (count aseq) labels))))
       aplan))

(defn make-contingent-tpn-from-plans
  [plans] ;+++ broken +++
  (let [rplans (reverse-labeling-of-plans plans)]
    ;;(println "make-contingent-tpn-from-plans with plans=" plans)
    (if (= (count rplans) 1)
      (encode-as-tpn [:sequence] rplans)
      ;; First divide the major parallel plans based on target
      (let [targetset (into #{} (map first rplans)) ;last
            _ (println "target set is: " targetset)
            threads (map (fn [target]
                           (remove nil?
                                   (map (fn [path]
                                          (if (= (first path) target) path)) ;last
                                        rplans)))
                         targetset)]
        ;;(println "In make-contingent-tpn-from-plans, threads=")
        (pprint threads)
        (case (count threads)
          0 nil
          1 (encode-as-tpn [:sequence] (first threads))
          `[:choose ~@(map (fn [thread] [:choice (encode-as-tpn [:sequence] thread)])
                           threads)])))))

(defn make-single-thread-tpn-from-plan
  [ap]
  ;; (println "single-thread ap=" ap)
  (let [sap (reverse-labeling-of-plans ap)]
    ;; (println "single-thread sap=" sap)
    (if (not (empty? sap))
      (encode-as-tpn [:sequence] sap)
      nil)))

;;; The (root) object containts the plan
(defn make-pclass-for-top
  [rpclass]
  [:pclass 'Top []
   [[:field 'top `(~rpclass)]]
   []])

;;; The (root) object containts the plan
(defn make-pclass-for-root
  [rpclass paname paclass pmethod-name args plans refs]
  [:pclass rpclass []
   `[[:field ~(symbol paname) (~paclass)]
     ~@(map (fn [aref] [:field aref (str aref)]) refs)]
   [[:pmethod pmethod-name args
     (let [pap (make-single-thread-tpn-from-plan plans)] ;make-contingent-tpn-from-plans or make-single-thread-tpn-from-plan
       (if pap (list pap) ()))]]])

;;; pclass-name is the class name of the solution
;;; pcargs is any arguments that thepclass expects
;;; pmethod-name is the solution method name
;;; args is the arglist for the pmethod
;;; plan is the generated plan
;;; mmap is the list of pmethods referred to in the plan and the number of arguments that they take

(defn make-pclass-for-tpn
  [pclass-name pcargs mmap]
  (let [pmethods
        (map (fn [[mname margs]]
               [:pmethod
                mname                   ; name
                (into [] (map (fn [n] (symbol (str "arg" (str n)))) (range 1 (+ margs 1)))) ; args
                ()])                    ; body
             mmap)]
    [:pclass pclass-name pcargs [] pmethods]))

(defn extract-field-name
  [plans]
  (first (into [] (apply set/union
                         (apply set/union (map (fn [plan]
                                                 (map (fn [acall]
                                                        #{ (first (string/split (str (second acall)) #"\.")) })
                                                      plan))
                                               plans))))))

(defn convert-plans-to-pamela
  [plans refs rpclass rmeth planningagent]
  (let [fname (extract-field-name plans)
        mmap (into {} (apply concat
                             (map (fn [plan]
                                    (map (fn [acall] { (symbol (last (string/split (str (second acall)) #"\.")))
                                                      (- (count (rest acall)) 1) })
                                         plan))
                                  plans)))]
    #_(println "In convert-plans-to-pamela with plans=" plans "refs=" refs "mmap=" mmap "fname=" fname)
    (list
     (convert-symbolic-tpn-to-pamela
      (make-pclass-for-top rpclass))
     (convert-symbolic-tpn-to-pamela
      (make-pclass-for-root rpclass fname planningagent rmeth nil plans refs))
     (convert-symbolic-tpn-to-pamela
      (make-pclass-for-tpn planningagent nil mmap)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn create-tpn-json-file-from-pamela [tpn-in-pamela goal]
  ;; Pamela should someday be extended so we didn't have to write and read these temporary files
  (let [pamela-file (java.io.File/createTempFile "pamela-source" ".pamela")
        tpn-json-file (java.io.File/createTempFile "pamela-json" ".tpn.json")
        [top-form attacker-form] tpn-in-pamela]
    (with-open [ostrm (clojure.java.io/writer pamela-file)]
      ;; Take advantage of the fact that Pamela uses the same basic syntax as Clojure
      (doseq [aform tpn-in-pamela]
        (pprint aform ostrm)))

    ;;For testing only
    ;; (reset! tpn/my-count (rand-int 10000))
    (pcli/tpn {:input [pamela-file]
               :output tpn-json-file
               :file-format "json"
               :construct-tpn (str "Top:top:" (str goal))})
    [pamela-file tpn-json-file]))

(defn extract-field-arguments
  [solutions]
  (into []
        (apply set/union
               (map (fn [plan]
                      (apply set/union
                             (map (fn [acall]
                                    (into #{}
                                          (remove nil?
                                                  (map (fn [arg] (if (symbol? arg) arg))
                                                       (rest acall)))))
                                  plan)))
                    solutions))))

(defn assemble-solutions
  [solutions rclass rmeth]
  #_(println "In assemble-solutions with rclass=" rclass "rmeth=" rmeth "solutions=" solutions)
  (let [refs (extract-field-arguments solutions)
        plans (into [] (translate-plan solutions))
        ;; jplans (json/write-str (into [] solutions))
        tpn-net-pamela (convert-plans-to-pamela plans refs rclass rmeth 'PlanningAgent)
        ;; _ (pprint tpn-net-pamela)
        tpn-files (create-tpn-json-file-from-pamela tpn-net-pamela rmeth)]
    ;;(pprint tpn-file)
    [tpn-net-pamela tpn-files]))

(defn make-tpn-from-solutions
  [solutions goal-root]
  (let [pamela-solutions (into #{} (map bir/compile-actionlist-to-pamela solutions))
        result (case (count pamela-solutions)
                 0 nil                  ; ["No solutions found"]
                 (assemble-solutions pamela-solutions goal-root 'goal))]
    result))

(defn generate-fresh-plan
  [goal-root samp maxd]
  ;; Make sure that we are in a good place wrt position of the player, etc
  ;; +++
  (let [maxt 0    ; where should we get this from? env-variable? startup parameter?
        solutions ;;(core/solveit :samples samp :max-depth maxd :rawp true)
                (core/mpsolveit :samples samp :max-depth maxd :rawp true :usethreads (if (= maxt 0) :maximum maxt))
        [symbpam [pamfile tpnfile]] (if solutions (make-tpn-from-solutions solutions goal-root))
        pamstr (if pamfile (slurp pamfile))
        tpnstr (if tpnfile (json/read-str (slurp tpnfile)))]
    (cond tpnstr                          ; if a solution was found
          [pamstr tpnstr]

          (and symbpam pamstr)
          (do
            (println "Error: generated pamela did not compile to a TPN:")
            (pprint symbpam))

          solutions
          (println "Error: Bad solution found: solution")

          :otherwise
          (println "No solutions found."))))
