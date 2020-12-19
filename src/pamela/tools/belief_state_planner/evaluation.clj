;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.evaluation
  "Evaluation"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [clojure.set :as set]
            [environ.core :refer [env]]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.prop :as prop]
            [pamela.tools.belief-state-planner.imagine :as imag]

            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.evaluation)

(declare deref-field)

(defn lookup-lvar
  "Search LVARS for a match with instance and name"
  [instance name]
  (let [found (filter #(and (= (:instance %) instance) (= (:field %) name)) @(global/.lvars global/*current-model*))]
    (if found
      (do
        #_(.write *out* (format "%n Found %s hence %s" (first found) (:value (first found))))
        (:value (first found)))
      (do
        #_(.write *out* (format "%n Failed to find %s.%s" instance name))
        name))))

(defn eval-arg
  "Evaluate the argument to a class."
  [arg instance]
  #_(.write *out* (format "%n In eval-arg: arg=%s instance=%s %n" arg instance))
  (cond
    (number? arg) arg
    (keyword? arg) arg
    (= (nth arg 0) :pclass-arg-keyword) (lookup-lvar instance (nth arg 1))
    :else arg))

;;; Should have made objects a map
(defn find-objects-of-name
  "Find all instantiated objects of a given type"
  [vname]
  (let [objects @(global/.objects global/*current-model*)]
    (remove nil? (map (fn [obj]
                        (if (= (.variable obj) vname) obj))
                      (seq objects)))))

(defn find-objects-of-type
  "Find all instantiated objects of a given type"
  [typename]
  (let [objects @(global/.objects global/*current-model*)]
    (remove nil? (map (fn [obj]
                        (if (= (.type obj) typename) obj))
                      (seq objects)))))

(defn maybe-get-named-object
  [val]
   (if (> global/verbosity 3) (println "In maybe-get-named-object with val=" val))
  (let [res (cond (string? val) ; +++ got to undo this string names and use symbols instead
                  (let [var (first (find-objects-of-name val))]
                    (when (nil? var)
                      (when (> global/verbosity 3)
                        (println "Didn't find object named" (prop/prop-readable-form val))
                        (doseq [anobj @(global/.objects global/*current-model*)]
                          (println (.variable anobj)))))
                    (or var val))

                  :otherwise val)]
    (if (and (> global/verbosity 3) (not (= val res)))
      (println "maybe-get-named-object var=" (prop/prop-readable-form val) "val=" (prop/prop-readable-form res)))
    res))


(defn instantiation-error
  [astring]
  (throw (Throwable. (str "Instantiation error: " astring))))

(declare instantiate-pclass)
(declare deref-field)

(defn get-likely-value
  [pdf threshold]
  (let [values (keys pdf)
        numvals (count values)]
    (if (> global/verbosity 3) (println "In get-likely-value pdf=" pdf "threshold=" threshold "values=" values "numvals=" numvals))
    (if (empty? pdf)
      :null
      (case numvals
        0 :null

        1 (first values)

        (let [best (apply max-key val pdf)]
          (if (>= (second best) threshold)
            (first best)
            :null))))))

(defn get-object-value
  "Gets the likely mode of the object - which must be an RTobject or a variable"
  [obj]
  (let [variable (cond (global/RTobject? obj) (.variable obj)
                       :otherwise obj)
        imagined (imag/get-mode variable)]
    (if imagined
      (do
        (if (> global/verbosity 3)
          (println "variable=" variable "imagined to have mode=" imagined))
        imagined)
      (let [pdf (bs/get-belief-distribution-in-variable variable)]
        (if (> global/verbosity 3)
          (println "variable=" variable "pdf=" pdf))
        (get-likely-value pdf 0.8)))))

(declare evaluate-reference)

(defn evaluate
  "Evaluate an expression in the current belief state with args as provided."
  [wrtobject path expn class-bindings method-bindings cspam spam]
  #_(println "\nIn evaluate with expn=" expn
             " path=" path
             " class-bindings=" class-bindings
             " method-bindings=" method-bindings)
  ;; (pprint spam)
  (case expn
    ;; Logical expressions
    :true true
    :false false

    (if (or (string? expn) (number? expn) (symbol? expn) (keyword? expn))
      expn
      (if (not (or (seq? expn) (vector? expn)))
        (if (map? expn)
          (let [vtype (get expn :type)]
            (case vtype
              :lvar (lvar/make-lvar (get expn :name))
              ;; :pclass-arg-ref
              ;; (let [names (get expn :names)
              ;;       argument (get class-bindings (first names))]
              ;;   ;; (println "Found argument " names " = " argument)
              ;;   (if (empty? (rest names))
              ;;     argument
              ;;     (deref-field (rest names) argument))) ;handle case where an indirect reference is made through a class arg
              :mode-ref
              (get expn :mode)

              (do (irx/error "Unknown form in Evaluate: " expn)
                  expn)))
          (irx/error "In evaluate: unexpected expression found: " expn))
        (case (first expn)
          ;; Constructors

          :make-lvar (lvar/make-lvar (second expn))

          :make-instance ; (:make-instance pname plant-id ... args)
          (let [cname (second expn)
                plant-id (nth expn 2)
                ;; - (println "in evaluate :make-instance with expn=" expn)
                class-spam (get (into {} spam) cname)
                classargs (get class-spam :args)
                numargs (count classargs)
                provided-args (drop 3 expn)
                extra-args (into {} (drop numargs provided-args))
                class-args (take numargs provided-args)
                id (get extra-args :id nil) ;+++ does nothing
                plant-part (get extra-args :plant-part nil)] ;+++ does nothing
            ;; (println "class-spam=" class-spam)
            ;; (println "provided-args=" provided-args)
            ;; (println "extra-args=" extra-args)
            ;; (println "plant-id=" plant-id)
            (if (> numargs (count class-args))
              (instantiation-error
               (str "missing arguments for pclass (" cname ") : " (str spam))))
            (instantiate-pclass
             wrtobject
             path
             cname
             spam
             class-spam
             class-bindings
             class-args ;(rest (rest expn))
             plant-id ;(last expn)
             plant-part)) ;+++ plant-part not implemented +++

          ;; logical Expressions
          :equal
          (let [res1 (evaluate wrtobject path (nth expn 1) class-bindings method-bindings cspam spam)
                res2 (evaluate wrtobject path (nth expn 2) class-bindings method-bindings cspam spam)]
            (if (= res1 res2) true false))

          :notequal
          (let [res1 (evaluate wrtobject path (nth expn 1) class-bindings method-bindings cspam spam)
                res2 (evaluate wrtobject path (nth expn 2) class-bindings method-bindings cspam spam)]
            (if (not (= res1 res2)) true false))

          :same
          (let [res1pre (evaluate-reference wrtobject (nth expn 1) class-bindings method-bindings cspam spam)
                res1 (if (global/RTobject? res1pre)
                       res1pre
                       (evaluate wrtobject path res1pre class-bindings method-bindings cspam spam))
                res2pre (evaluate-reference wrtobject (nth expn 2) class-bindings method-bindings cspam spam)
                res2 (if (global/RTobject? res2pre)
                       res2pre
                       (evaluate wrtobject path res2pre class-bindings method-bindings cspam spam))]
            (if (= res1 res2) true false))

          :notsame
          (let [res1pre (evaluate-reference wrtobject (nth expn 1) class-bindings method-bindings cspam spam)
                res1 (if (global/RTobject? res1pre)
                       res1pre
                       (evaluate wrtobject path res1pre class-bindings method-bindings cspam spam))
                res2pre (evaluate-reference wrtobject (nth expn 2) class-bindings method-bindings cspam spam)
                res2 (if (global/RTobject? res2pre)
                       res2pre
                       (evaluate wrtobject path res2pre class-bindings method-bindings cspam spam))]
            (if (not (= res1 res2)) true false))

          :not
          (let [res (evaluate wrtobject path (nth expn 1) class-bindings method-bindings cspam spam)]
            (if res false true))

          :or (if (some #(evaluate wrtobject path % class-bindings method-bindings cspam spam) (rest expn))
                true
                false)

          :and (if (every? #(evaluate wrtobject path % class-bindings method-bindings cspam spam) (rest expn))
                 true
                 false)

          ;; General Expressions
          :value (let [val (second expn)]
                   (if (not (global/RTobject? val)) val (get-object-value val)))

          :thunk (evaluate (nth expn 2) path (second expn) class-bindings method-bindings cspam spam)

          ;; :or (if (= (count (rest expn)) 1)
          ;;       (evaluate wrtobject path (second expn) class-bindings method-bindings cspam spam)
          ;;       :true) ;+++ this is not finished +++ only the trivial case is implemented

          :class-arg (let [res (get class-bindings (second expn))]
                       (if (and (not (number? res)) (not (symbol? res)) (not (keyword? res)) (empty? res))
                         (irx/error "In evaluate with " expn "class-bindings=" class-bindings "res=" res))
                       res)

          :field (let [value (deref-field (rest expn) wrtobject :normal)]
                   (if (not (global/RTobject? value)) value (get-object-value value)))

          :arg-field (let [[object & field] (rest expn)
                           - (if (> global/verbosity 2)
                               (println "Evaluate :arg-field object= " (prop/prop-readable-form object)
                                        "field=" field "expn=" (prop/prop-readable-form expn)))
                           obj (cond
                                 (global/RTobject? object)
                                 object

                                 (string? object)
                                 (maybe-get-named-object object)

                                 (= (first object) :value)
                                 (second object)

                                 :otherwise
                                 (deref-field (rest object) #_wrtobject (second (first (global/get-root-objects))) :normal)) ; Force caller to be root+++?
                           - (if (> global/verbosity 2) (println ":arg-field obj= " (prop/prop-readable-form obj)))
                           value (maybe-get-named-object (deref-field field obj :normal))
                           ] ; +++ handle multilevel case
                         (if (not (global/RTobject? value)) value (get-object-value value)))

          :mode-of (last expn)

          :function-call (do
                           (println "evaluate: :function-call")
                           (pprint expn)
                           true)

          :arg nil                            ; method arg NYI
          :field-ref (do (irx/error "UNEXPECTED: Found a field ref: " expn) nil)

          ;; Arithmetic Expressions
          ;; goe here!

          (do
            (irx/error "Evaluate: Unknown case: " expn)
            nil))))))                               ; unrecognised defaults to nil

(defn evaluate-reference
  "evaluate an expression in the current belief state with args as provided to provide a reference."
  [wrtobject expn class-bindings method-bindings cspam spam]
  #_(println "\nIn evaluate-reference with expn=" expn
             " class-bindings=" class-bindings
             " method-bindings=" method-bindings)
  ;; (pprint spam)
  (case expn
    :true [:value true]

    :false [:value false]

    (if (or (string? expn) (number? expn))
      [:value expn]
      (if (not (or (seq? expn) (vector? expn)))
        (if (map? expn)
          (let [vtype (get expn :type)]
            (case vtype
              :mode-ref expn

              :lvar (irx/error "evaluate-reference: lvar constructor found where it wasn't expected: " expn)
              (do (irx/error "evaluate-reference: Unknown form in Evaluate: " expn) expn)))
          (irx/error "evaluate-reference: unexpected expression:" expn))

        (case (first expn)
          :thunk (evaluate-reference (nth expn 2) (second expn) class-bindings method-bindings cspam spam)
          :make-instance (irx/error "evaluate-reference: constructor found where it wasn't expected: expn")

          ;; :or (some #(evaluate wrtobject "???" % class-bindings method-bindings cspam spam) (rest expn))
          ;; :and (every? #(evaluate wrtobject "???" % class-bindings method-bindings cspam spam) (rest expn))

          :class-arg (let [res (get class-bindings (second expn))]
                       (if (and (not (symbol? res)) (not (keyword? res)) (empty? res))
                         (irx/error "In evaluate-reference with " expn "class-bindings=" class-bindings "res=" res))
                       res)

          :field (let [value (deref-field (rest expn) wrtobject :reference)]
                   (if (not (global/RTobject? value)) value [:value value]))

          :arg-field (let [[object & field] (rest expn)
                           - (if (> global/verbosity 2)
                               (println "Evaluate-reference :arg-field object= " (prop/prop-readable-form object)
                                        "field=" field "expn=" (prop/prop-readable-form expn)))
                           obj (cond
                                   (global/RTobject? object)
                                   object

                                   (string? object)
                                   (maybe-get-named-object object)

                                   (and (vector? object) (= (first object) :value))
                                   (second object) ;+++ Surely, this should be object, not second object

                                   (and (vector? object) (= (first object) :arg-field))
                                   (evaluate-reference wrtobject object class-bindings method-bindings cspam spam)

                                   :otherwise
                                   (deref-field (rest object) (second (first (global/get-root-objects))) :reference)) ; Force caller to be root+++?
                           - (if (> global/verbosity 2)
                               (println ":arg-field field=" field "obj=" (prop/prop-readable-form obj)))
                           value (deref-field field obj :reference)] ; +++ handle multilevel case NYI
                         (if (not (global/RTobject? value)) value [:value value]))

          :mode-of [:value (last expn)]

          :value expn

          :function-call (irx/error "Unhandled case: " expn)

          (irx/error "Evaluate-reference Unknown case: " expn))))))


(defn evaluate-arg
  [arg wrtobject class-args]
  ;; (println "In evaluate-arg with arg=" arg "class-args=" class-args)
  (case (:type arg)
    :field-ref (deref-field (:names arg) wrtobject :normal)
    :pclass-arg-ref
    (let [names (get arg :names)
          argument (get class-args (first names))]
      ;; (println "Found argumentx " names " = " argument)
      (if (empty? (rest names))
        argument
        :shit))
    ;; +++ need to enumerate all possible cases, here
    arg))

(defn initial-mode-of
  [modes class-bindings method-bindings cspam spam]
  (let [emodes (remove nil? (map (fn [[mode val]] (if (= val :initial) mode nil)) modes))
        initial (first emodes)]
    (if (> global/verbosity 3)
      (println "initial-mode-of modes=" modes " emodes =" emodes " initial=" initial))
    (or initial (first (first modes)))))

(defn compute-dependencies
  [init]
  ;; (println "Computing dependencies of:" init)
  (if (vector? init)
    (cond (= (first init) :make-instance)
          (set (remove nil? (concat (map (fn [anarg]
                                       (cond (= (:type anarg) :field-ref) (first (:names anarg))
                                             (= (:type anarg) :field) (first (:names anarg)) ; should never occur
                                             :else nil))
                                         (rest (rest init))))))

          (= (first init) :field) (set (list (second init)))
          :else nil)
    (case (:type init)
      pclass-ctor
      (let [args (:args init)
            frefs (remove nil? (concat (map (fn [anarg]
                                              (cond (= (:type anarg) :field-ref) (first (:names anarg))
                                                    (= (:type anarg) :field) (first (:names anarg)) ; this case should never occur

                                                    :else nil))
                                            args)))]
        (set frefs))
      (set nil))))

(defn instantiate-pclass
  "Create an instance of a model class."
  [wrtobject path cname spam class-spam class-bindings args id plant-part]
  ;; (println "****** in instantiate-pclass with path=" path "cname=" cname "args=" args)
  ;; (pprint class-spam)
  (let [classargs (get class-spam :args)
        numargs (count classargs)
        ;; - (println "***!!! In instantiate-pclass, args=" args)
        argmap  (into {} (map #(vector %1 (evaluate-arg %2 wrtobject class-bindings)) classargs (take numargs args)))
        ;; - (println "***!!! argmap=" argmap)
        cfields (seq (map (fn [[fname fdef]] [fname fdef]) (get class-spam :fields)))
        modes (seq (get class-spam :modes))
        ;; The instance name captures the hierarchy of the object in nested structures
        ;; Non embedded objects are at the root level and are named after their class with a proceeding "/"
        instance-name path
        newObject (global/make-object instance-name cname nil id)]
    (if (> global/verbosity 1)
      (.write *out* (format "%nInstantiating class %s%n  args=%s%n  id=%s%n  fields=%s%n  modes=%s%n"
                            cname argmap id cfields modes)))
    ;; Create an instance var for the instatiated class and add it to the belief state and the model objects
                                        ;(if modes
    (do
      ;; (.write *out* (format "%nAdding variable: %s %s %s%n" instance-name cname (map first modes)))
      (bs/add-variable instance-name cname (map first modes))
      (when modes (bs/set-belief-in-variable instance-name
                                             (initial-mode-of modes argmap nil class-spam spam)
                                             1.0))
      (bs/add-binary-proposition :is-a instance-name (str cname))) ;)
    (global/add-object newObject)
    (if id (global/add-plant id newObject)) ;+++ what do we do with plant-part?
    ;;(println "cfields=" cfields)
    (let [field-vector (seq (map (fn [[fname fdef]]
                                   (let [initial (:initial fdef)
                                         value (atom initial)
                                         dependson (compute-dependencies initial)]
                                     [fname value dependson]))
                                 cfields))
          field-map (into {} (map (fn [[fname value dep]] [fname value]) field-vector))]
      ;;(println "Computed field dependencies: " field-vector)
      (reset! (.fields newObject) field-map)
      ;; Now populate the fields. Fields are computed sequentially to enable prior fields to be referenced
      (let [satisfied (atom (set nil))
            touched (atom true)]
        (while @touched
          (reset! touched false)
          (doseq [afield field-vector]
            (let [[fname valatom dependson] afield
                  initial @valatom]
              (if (and initial
                       (empty? (clojure.set/difference dependson @satisfied))
                       (not (@satisfied fname)))
                (do
                  ;; (println "Evaluating field: " fname)
                  (reset! touched true)
                  (reset! satisfied (conj @satisfied fname))
                  (reset! valatom (evaluate newObject (str instance-name "." fname) initial argmap nil class-spam spam)))))))
        ;; (println "Satisfied=" @satisfied "touched=" @touched "field-vector:")
        ;; (pprint field-vector)
        )
      ;; (println "Here are the fields that we found: " fields)
      newObject)))

(defn maybe-deref
  [thing mode]
  (let [derefedthing
        (if (= (type thing) clojure.lang.Atom)
          @thing
          thing)
        deboundthing
        (if (and (not (= mode :reference)) (lvar/is-lvar? derefedthing) (lvar/is-bound-lvar? derefedthing))
          (lvar/deref-lvar derefedthing)
          derefedthing)]
    deboundthing))

(def ^:dynamic ***namelist*** :debug)
(def ^:dynamic ***wrtobject*** :debug)

(defn deref-field
  [namelist wrtobject mode]
  (if (> global/verbosity 2)
    (println "deref-field: " namelist
             "wrt-object=" (if (global/RTobject? wrtobject)
                             (.variable wrtobject)
                             [:oops wrtobject])
             "mode=" mode))
  (cond
    (and (vector? (first namelist)) (= (first (first namelist)) :value))
    (second (first namelist))

    ;; (string? namelist) ; +++ don't like this string references.
    ;;                    ;; We should something to the syntax to remove ambiguity.
    ;; (let [result (maybe-get-named-object namelist)]
    ;;   result)

    (vector? wrtobject)
    (do (irx/error "dereference failed on bad wrtobject=" (prop/prop-readable-form wrtobject))
        [:not-found namelist])

    (empty? wrtobject)
    (do
      (irx/error "trying to dereference " namelist "with null wrtobject!")
      [:not-found namelist])

    :otherwise
    (let [fields (.fields wrtobject)
          ;; _ (println "***!!! namelist=" namelist " fields = " @fields)
          match (get @fields (first namelist))
          imagined (imag/get-field-value (global/RTobject-variable wrtobject) (first namelist))
          ;; _ (println "***!!! found match for" (first namelist)  " = " match)
          remaining (rest namelist)]
      (if (empty? remaining)
        (do
          ;; (println "***!!! dereferenced " (first namelist)
          ;;          "=" (prop/prop-readable-form match))
          (if (= match nil)
            (irx/error "DEREF ERROR: [:not-found" namelist ":in" (prop/prop-readable-form wrtobject) "]")
            (or imagined @match)))
        (do
          (if (not (= match nil))
            (do
              (if (lvar/is-lvar? @match)
                (if (lvar/is-bound-lvar? @match)
                  (deref-field remaining (maybe-get-named-object (lvar/deref-lvar @match)) mode)
                  (irx/error "DEREF ERROR: attempt to dereference unbound LVAR:" (lvar/lvar-string @match)))
                (do
                  ;; (println "***!!! recursive dereference with object=" @match)
                  (deref-field remaining (or imagined @match) mode))))
            (do
              (def ^:dynamic ***namelist*** namelist)
              (def ^:dynamic ***wrtobject*** wrtobject)
              (irx/error [:not-found namelist :in (prop/prop-readable-form wrtobject)]))))))))

(defn field-exists
  [names wrtobject]
  (let [result (deref-field names wrtobject :normal)]
    (not (and (vector? result) (= (count result) 2) (= (first result) :not-found)))))

(defn lookup-class
  [cname]
  (let [pclass-defs (into {} @(global/.pclasses global/*current-model*))]
    (get pclass-defs cname)))

(defn deref-method
  [names wrtobject]
  (let [object (if (= (count names) 1)
                 wrtobject
                 (deref-field (take (- (count names) 1) names) wrtobject :normal))]
    (if (not (global/RTobject? object))
      [:not-found names]
      (let [classname (:type object)
            class-def (lookup-class classname)]
        (if (= class-def nil)
          [:not-found classname]
          (let [methods (:methods class-def)
                sought (last names)
                method-names (into #{} (map (fn [method] (irx/.mname method)) methods))]
            ;;(println "Method names found = " method-names " method sought =" sought)
            (if (get method-names sought)
              :found
              [:not-found (last names)])))))))

(defn method-exists
  [names wrtobject]
  (let [result (deref-method names wrtobject)]
    (not (and (vector? result) (= (count result) 2) (= (first result) :not-found)))))
