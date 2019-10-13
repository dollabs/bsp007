;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.runtimemodel
  "Runtime Model"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [clojure.java.io :as io]
            [environ.core :refer [env]]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.runtimemodel)

(defrecord RuntimeModel [lvars
                         objects
                         plantmap
                         pclasses
                         pre-and-post-conditions
                         invertedinfluencehashtable
                         rootclass])

;;; was (defrecord RuntimeModel [lvars objects plantmap])
(defrecord RTobject [variable type fields id])

(defrecord LVar [name binding boundp])

;;(def ^:dynamic *printdebug* true)
(def ^:dynamic *printdebug* false)

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
;;; was (def ^:dynamic *current-model* (RuntimeModel. (atom nil) (atom nil) (atom {})))

(defn unload-model
  "Delete the current model if any."
  []
  ;; For every instantiated object delete its mode variable.
  (doseq [obj (seq @(.objects *current-model*))]
    (let [pclass (:class obj)
          mode (:mode obj)]
      (if *printdebug*
        (.write *out* (format "%nMode of %s: %s" pclass mode)))
      ;; Delete the belief in the objects mode
      (bs/undef-variable mode)
      ))
  (reset! (.lvars *current-model*) nil)
  (reset! (.objects *current-model*) nil)
  (reset! (.plantmap *current-model*) {})
  (reset! (.pclasses *current-model*) {})
  (reset! (.pre-and-post-conditions *current-model*) {})
  (reset! (.invertedinfluencehashtable *current-model*) {})
  (reset! (.rootclass *current-model*) nil))

(defn goal-post-conditions
  []
  (second @(.pre-and-post-conditions *current-model*)))

(defn inverted-influence-table
  []
  @(.invertedinfluencehashtable *current-model*))

(defn get-root-class-name
  []
  @(.rootclass *current-model*))

(defn get-root-objects
  "Returns the root object."
  []
  (let [objects @(.plantmap *current-model*)]
    (remove nil? (map (fn [[id rtobj]]
                        (if (= id "root") [id rtobj] nil))
                      objects))))

(defn get-root-fields
  []
  (let [root (second (first (get-root-objects)))
        fields @(.fields root)]
    fields))

 (defn get-field-value
  [objectname fieldname]
  (let [objects (get-root-fields)
        named-object @(get objects objectname)
        named-object-fields @(.fields named-object)
        value @(get named-object-fields fieldname)]
    value))

#_(defn set-field-value
  [objectname fieldname newvalue]
  (let [objects (get-root-fields)
        named-object @(get objects objectname)
        named-object-field
        s @(.fields named-object)
        value (get named-object-fields fieldname)]
    (swap! value newvalue)
    value))

(defn group-by-first-equal
  "Create a hash map where clashes map onto a list, in linear time."
  [pairs]
  (let [keys (into #{} (seq (map first pairs))) ; get a list of keys
        h-map (into (hash-map) (seq (map (fn [key] [key (atom nil)]) keys)))] ; Create atoms for each entry
    ;; Iterate through each value putting it in its place.
    (doseq [[key val] pairs]
      (let [pval (get h-map key)]
        (reset! pval (cons val @pval))))
    ;; A final pass to produce an immutable hash-map result.
    (into (hash-map) (map (fn [[k v]] [k @v]) h-map))))

(defn get-inverse-root-field-type-map
  []
  (let [root-fields (get-root-fields)
        field-type-map (remove nil? (map (fn [[name obj]]
                                           (if (instance? RTobject @obj)
                                             [(.type @obj) name]
                                             nil))
                                         root-fields))]
    (group-by-first-equal field-type-map)))

(defn get-root-objects-of-type
 [objtype]
 (let [invrftm (get-inverse-root-field-type-map) ;+++ cache this to avoid recalc +++
       matchobjs (get invrftm objtype)]
   matchobjs))

(defn describe-rtobject
  "Describe a runtime object."
  [rto]
  (let [variable (.variable rto)
        type (.type rto)
        fields @(.fields rto)
        id (.id rto)]
    (.write *out* (format "%n <RTobject variable=%s type=%s id=%s%n   fields={ " variable type id))
    (doseq [[fname fval] fields]
      (.write *out* (format "%n    %s %s " fname @fval)))
    (.write *out* (format "}>"))))

(declare describe-lvar)

(defn describe-current-model
  "Print out a description of the currently loaded model."
  []
  (let [lvars @(.lvars *current-model*)
        rootclass @(.rootclass *current-model*)
        objects @(.objects *current-model*)
        [pre post] @(.pre-and-post-conditions *current-model*)
        iiht @(.invertedinfluencehashtable *current-model*)]
    (.write *out* (format "%nCurrent model:%n%nLVARS:%n"))
    (doseq [lvar (seq lvars)]
      (describe-lvar lvar))
    (.write *out* (format "%n%nOBJECTS:%n"))
    (doseq [obj (seq objects)]
      (describe-rtobject obj))
    (when (not (= (second pre) true))
      (.write *out* (format "%n%nPRECONDITION:%n"))
      (pprint pre))
    (when (not (= (second post) true))
      (.write *out* (format "%n%nPOSTCONDITION:%n"))
      (pprint post))
    (when iiht
      (.write *out* (format "%n%nInverted Influence Map: %n"))
      (pprint iiht))
    (.write *out* (format "%n%nPlant Map: %n"))
    (doseq [[k v] @(.plantmap *current-model*)]
      (.write *out* (format "%nPlant ID: %s = %s" k v)))))

(defn in?
  "true if coll contains elm"
  [coll elm]
  (some #(= elm %) coll))

(defn add-object
  "Add an object to the current model."
  [object]
  ;;  (if (not (in? (.objects *current-model*) object))
  (reset! (.objects *current-model*) (cons object @(.objects *current-model*)))
  ) ;;)

(defn add-lvar
  "Add an lvar to the current model."
  [lv]
  ;;  (if (not (in? (.lvars *current-model*) lv))
  (reset! (.lvars *current-model*) (cons lv @(.lvars *current-model*)))
  ) ;;)

(defn add-pclasses
  "Add an pclasses from a loaded model file."
  [pcs]
  (if *printdebug*
    (do (println "adding spam:\n")
        (pprint pcs)))
  (reset! (.pclasses *current-model*) pcs)) ;+++ unfinished, thsi needs to merge with wgats already there

(defn add-preandpost
  "Add a preandpost condition vector from a loaded model file."
  [ppcs]
  (if *printdebug*
    (do
      (println "adding pre-and-post-conditions:\n")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lvar implementation

(defn make-lvar
  [name]
  (let [lv (LVar. name (atom nil) (atom :unbound))]
    (add-lvar lv)
    lv))

(defn deref-lvar
  [something]
  (if (instance? LVar something)
    (if (= @(.boundp something) :unbound)
      something
      (deref-lvar @(.binding something)))
    something))

(defn bind-lvar
  [lv nval]
  (if (= @(.boundp lv) :unbound)
    (do
      (reset! (.boundp lv) :bound)
      (reset! (.binding lv) (deref-lvar nval)))
    (let [boundto (deref-lvar lv)]
      (if (instance? LVar boundto)
        (bind-lvar boundto nval)
        (= boundto (deref-lvar nval))))))

(defn describe-lvar
  [lv]
  (.write *out* (format "<LVAR name=%s%s%s>%n"
                        (.name lv)
                        (if (= @(.boundp lv) :unbound) "" " value=")
                        (if (= @(.boundp lv) :unbound) "" @(.binding lv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Extraction for the planner

(defn get-goal-pre-and-post-conditions
  "Returns a vector of two objects: [preconditions postconditions]."
  []
  ;; Find the root, it should have a single method whose pre and post conditions
  ;; represent the planning goal.  The planner effectively computes the body for this method
  ;; such that compiling the file, with the produced body and invoking the method should
  ;; solve the problem.
  ;; Find the root class given the name.
  ;; Find its method
  ;; Extract its pre and post conditions
  ;; return [pre post]
  (.pre-and-post-conditions *current-model*))

(defn controllable-object?
  "This is a test that the object in question is controllable by the planner. REWRITE+++"
  [id rtobj]
  (let [idname (str id)]
    (Character/isUpperCase (first idname))))

(defn get-controllable-objects
  "Returns a sequence of all of the controllable objects."
  []
  (let [objects @(.plantmap *current-model*)]
    (remove nil? (map (fn [[id rtobj]]
                        (if (controllable-object? id rtobj) [id rtobj] nil))
                      objects))))

(defn get-class-by-name
  [name]
  (let [current-classes (into {} @(.pclasses *current-model*))
        class (get current-classes (symbol name))]
    class))

(defn get-methods-of-class
  [name]
  (let [class (get-class-by-name name)
        methods (get class :methods)]
    methods))

(defn get-controllable-methods
  "Returns a list of tuples [pclass pmethod object] for each controllable method."
  []
  (let [c-objects (get-controllable-objects)]
    (apply concat
           (map (fn [[id rtobj]]
                  (let [pclass (.type rtobj)
                        methods (get-methods-of-class pclass)]
                    (map (fn [method] [pclass method rtobj]) methods)))
                c-objects))))

(defn get-root-methods
  "Returns a list of tuples [pclass pmethod object] for each root method."
  []
  (let [r-objects (get-root-objects)]
    (apply concat
           (map (fn [[id rtobj]]
                  (let [pclass (.type rtobj)
                        methods (get-methods-of-class pclass)]
                    (map (fn [method] [pclass method rtobj]) methods)))
                r-objects))))

(defn describe-controllable-methods
  []
  (map
   (fn [[pcls mthd rtobj]]
     (pprint mthd))
   (get-controllable-methods)))

(defn extract-referents
  [condition]
  (remove nil? (map
                (fn [val]
                  (if (vector? val)
                    (case (first val)
                      :field val
                      :mode-of :mode
                      :arg nil
                      :arg-field val
                      nil)))
                (rest condition))))

(defn compile-influence
  [condition]
  (if (vector? condition)               ;atomic conditions = no influence
    (case (first condition)
      :equal (cond (or (and (= (first (nth condition 1)) :arg)
                            (= (first (nth condition 2)) :mode-of))
                       (and (= (first (nth condition 2)) :arg)
                            (= (first (nth condition 1)) :mode-of)))
                   (list [:arg-mode])
                   (and (= (first (nth condition 1)) :field)) (list (nth condition 1))
                   (and (= (first (nth condition 2)) :field)) (list (nth condition 2))
                   (and (= (first (nth condition 1)) :arg-field)) (list (nth condition 1))
                   (and (= (first (nth condition 2)) :arg-field)) (list (nth condition 2))
                   :else (list (extract-referents condition)))
      :and (apply concat (map (fn [arg] (compile-influence arg)) (rest condition)))
      :mode-of (list [:mode])
      :not (list [:not]) ;+++
      nil)))

(defn controllable-method-influence-table
  "Compile controllable methods into an influence table."
  []
  (let [c-methods (get-controllable-methods)]
    (remove nil? (map (fn [[pclass pmethod rtobj]]
                        [(irx/.mname pmethod) pclass (compile-influence (irx/.postc pmethod))])
                      c-methods))))

(defn root-method-influence-table
  "Compile root methods into an influence table."
  []
  (let [r-methods (get-root-methods)]
    (remove nil? (map (fn [[pclass pmethod rtobj]]
                        (let [[mname pre post prob args] pmethod]
                          [(first pmethod) pclass (compile-influence post)]))
                      r-methods))))

;;; (group-by-first-equal [[:a 1][:b 2][:c 3][:a 4][:b 5]]) => {:c (3), :b (5 2), :a (4 1)}

(defn inverted-method-influence-table
  "Returns a table mapping fields and modes to methods that affect them."
  []
  (let [inf-table (controllable-method-influence-table)
        eff-table (apply concat
                         (map (fn [[pmeth pcls effects]]
                                (map (fn [effect]
                                       (if (or (= (first effect) :arg-mode)
                                               (= (first effect) :arg-field))
                                         [[:any effect] pmeth]
                                         [[@(.rootclass *current-model*) effect] pmeth])) ; +++was pcls
                                     effects))
                              inf-table))]
    (group-by-first-equal eff-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn lookup-lvar
  "Search LVARS for a match with instance and name"
  [instance name]
  (let [found (filter #(and (= (:instance %) instance) (= (:field %) name)) @(.lvars *current-model*))]
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

;;; was (defn make-arglist
;;; was   "Construct an arglist from an initial field constructor"
;;; was   [pcarglist args instance]
;;; was   (if (= (count pcarglist) 0)
;;; was     nil
;;; was     (let [alist (seq (map #(vector %1 (eval-arg %2 instance)) (seq pcarglist) (seq args)))]
;;; was       #_(.write *out* (format "%n In make-arglist: Arglist=%s Args=%s result=%s %n" pcarglist args alist))
;;; was       alist)))

;; (defn make-arglist ;; +++ not used
;;   "Construct an arglist from an initial field constructor"
;;   [pcarglist args instance]
;;   (if (= (count pcarglist) 0)
;;     nil
;;     (let [alist (seq (map #(vector %1 (eval-arg %2 instance)) (seq pcarglist) (seq args)))]
;;       #_(.write *out* (format "%n In make-arglist: Arglist=%s Args=%s result=%s %n" pcarglist args alist))
;;       alist)))

;; (defn make-lvar  ;; +++ not used
;;   "Construct an lvar object"
;;   [instance field aname]
;;   (let [varname (gensym (:name aname))]
;;     (bs/add-variable varname (:name aname) nil)
;;     {:lvar (:name aname) :value varname :instance instance :field field}))

(defn initial-mode-of
  [modes class-bindings method-bindings cspam spam]
  (let [emodes (remove nil? (map (fn [[mode val]] (if (= val :initial) mode nil)) modes))
        initial (first emodes)]
    ;; (println "initial-mode-of modes=" modes " emodes =" emodes " initial=" initial)
    (or initial (first (first modes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Evaluators

(declare instantiate-pclass)
(declare deref-field)

(defn instantiation-error
  [astring]
  (throw (Throwable. (str "Instantiation error: " astring))))

(defn evaluate
  "Evaluate an expression in the current belief state with args as provided."
  [wrtobject expn class-bindings method-bindings cspam spam]
  #_(println "\nIn evaluate with expn=" expn
             " class-bindings=" class-bindings
             " method-bindings=" method-bindings)
  ;; (pprint spam)
  (case expn
    :true true
    :false false
    (if (or (string? expn) (number? expn))
      expn
      (if (not (or (seq? expn) (vector? expn)))
        (if (map? expn)
          (let [vtype (get expn :type)]
            (case vtype
              :lvar (make-lvar (get expn :name))
              ;; :pclass-arg-ref
              ;; (let [names (get expn :names)
              ;;       argument (get class-bindings (first names))]
              ;;   ;; (println "Found argument " names " = " argument)
              ;;   (if (empty? (rest names))
              ;;     argument
              ;;     (deref-field (rest names) argument))) ;handle case where an indirect reference is made through a class arg
              (do (println "ERROR: Unknown form in Evaluate: " expn)
                  expn)))
          nil) ;+++ we shouldn't get here
        (case (first expn)
          :make-instance ; (:make-instance pname plant-id ... args)
          (let [cname (second expn)
                plant-id (nth expn 2)
                ;; - (println "in evaluage :make-instance with expn=" expn)
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
             cname
             spam
             class-spam
             class-bindings
             class-args ;(rest (rest expn))
             plant-id ;(last expn)
             plant-part)) ;+++ plant-part not implemented +++
          :or (if (= (count (rest expn)) 1)
                (evaluate wrtobject (second expn) class-bindings method-bindings cspam spam)
                :true) ;+++ this is not finished +++ only the trivial case is implemented
          :arg nil                            ; method arg NYI
          :class-arg (let [res (get class-bindings (second expn))]
                       (if (and (not (symbol? res)) (not (keyword? res)) (empty? res))
                         (println "ERROR: In evaluate with " expn "class-bindings=" class-bindings "res=" res))
                       res)
          :field-ref (do (println "UNEXPECTED: Found a field ref: " expn) nil)
          :field (deref-field (rest expn) wrtobject)
          :mode-of (last expn)
          :make-lvar (make-lvar (second expn))
          :function-call (do
                           (println "evaluate: :function-call")
                           (pprint expn)
                           true)
          (do
            (println "ERROR: Unknown case: " expn)
            nil))))))                               ; unrecognised defaults to nil

(defn maybe-deref
  [thing]
  (if (= (type thing) clojure.lang.Atom)
    @thing
    thing))

(defn deref-field
  [namelist wrtobject]
  (if (vector? wrtobject)
    (do (println "ERROR: dereference failed on bad wrtobject=" wrtobject)
        [:not-found namelist])
    (if (empty? wrtobject)
      (do
        (println "ERROR: trying to dereference " namelist "with null wrtobject!")
        [:not-found namelist])
      (let [fields (.fields wrtobject)
            ;; - (println "***!!! fields = " @fields)
            match (get @fields (first namelist) )
            ;;- (println "***!!! found match for" (first namelist)  " = " match)
            remaining (rest namelist)]
        (if (empty? remaining)
          (do
            ;; (println "***!!! dereferenced " (first namelist) "=" (maybe-deref match))
            (if (= match nil)
              [:not-found namelist]
              (maybe-deref match)))
          (do
            (if (not (= match nil))
              (do
                ;; (println "***!!! recursive dereference with object=" @match)
                (deref-field remaining @match))
              [:not-found namelist])))))))

(defn field-exists
  [names wrtobject]
  (let [result (deref-field names wrtobject)]
    (not (and (vector? result) (= (count result) 2) (= (first result) :not-found)))))

(defn lookup-class
  [cname]
  (let [pclass-defs (into {} @(.pclasses *current-model*))]
    (get pclass-defs cname)))

(defn deref-method
  [names wrtobject]
  (let [object (if (= (count names) 1)
                 wrtobject
                 (deref-field (take (- (count names) 1) names) wrtobject))]
    (if (not (instance? RTobject object))
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


(defn evaluate-arg
  [arg wrtobject class-args]
  ;; (println "In evaluate-arg with arg=" arg "class-args=" class-args)
  (case (:type arg)
    :field-ref (deref-field (:names arg) wrtobject)
    :pclass-arg-ref
    (let [names (get arg :names)
          argument (get class-args (first names))]
      ;; (println "Found argumentx " names " = " argument)
      (if (empty? (rest names))
        argument
        :shit))
    ;; +++ need to enumerate all possible cases, here
    arg))

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
  [wrtobject cname spam class-spam class-bindings args id plant-part]
  ;; (println "****** in instantiate-pclass with args=" args)
  ;; (pprint class-spam)
  (let [classargs (get class-spam :args)
        numargs (count classargs)
        ;; - (println "***!!! In instantiate-pclass, args=" args)
        argmap  (into {} (map #(vector %1 (evaluate-arg %2 wrtobject class-bindings)) classargs (take numargs args)))
        ;; - (println "***!!! argmap=" argmap)
        cfields (seq (map (fn [[fname fdef]] [fname fdef]) (get class-spam :fields)))
        modes (seq (get class-spam :modes))
        instance-name (or (gensym cname) nil)
        newObject (RTobject. instance-name cname (atom nil) id)]
    (if *printdebug*
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
      (bs/add-binary-proposition :is-a instance-name cname)) ;)
    (add-object newObject)
    (if id (add-plant id newObject)) ;+++ what do we do with plant-part?
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
                  (reset! valatom (evaluate newObject initial argmap nil class-spam spam)))))))
        ;; (println "Satisfied=" @satisfied "touched=" @touched "field-vector:")
        ;; (pprint field-vector)
        )
      ;; (println "Here are the fields that we found: " fields)
      newObject)))


(defn get-field-atom
  "Find the atom represented by the specified field name in the RTobject provided."
  [object field]
  (let [fields @(.fields object)
        fieldatom (get fields field)]
    #_(if fieldatom
      (.write *out* (format "%nFound field %s = %s !!!%n" field fields))
      (.write *out* (format "%nField %s not found in %s !!!%n" field fields)))
    fieldatom))

(defn load-model-from-json-string
  [json-string root args]
  (let [ir (irx/read-ir-from-json-string json-string)
        spam (irx/json-ir-to-spamela ir false)]
    (add-pclasses spam)
    (if (not (= ir nil))
      (do
        ;; Get the modes from the model and create them in the BS
        (let [modes (irx/get-modes-from-ir ir)]
          (doseq [amode (seq modes)]
            ;; (.write *out* (format "%nModes of class %s: %s" (:pclass amode) (pr-str (map first (:values amode)))))
            (bs/add-domain (:pclass amode) (apply list (map first (:values amode))))))
        ;; If root is provided:
        ;;    execute (root)
        (if (not (= root nil))
          (do
            (let [rootsym (symbol root)
                  ;; _ (pprint root)
                  sroot [rootsym []]
                  ;; _ (pprint sroot)
                  root-class (irx/get-spamela-class-from-ir ir sroot)
                  ;; _ (pprint root-class)
                  root-methods (get root-class :methods)
                  ;; _ (pprint root-methods)
                  goal-method (first root-methods)
                  ;; _ (pprint  goal-method)
                  pre-and-post (if (and root-class goal-method)
                                 [[rootsym (irx/.prec goal-method)] [rootsym (irx/.postc goal-method)]])]
              (if root-class
                (do
                  (reset! (.rootclass *current-model*) rootsym)
                  (add-preandpost pre-and-post)
                  #_(.write *out* (format "%nRoot class %s, found %s" sroot
                                          (with-out-str (pprint root-class))))
                  (instantiate-pclass nil (first sroot) spam root-class nil args "root" "root-part")
                  ;; Now establish the inverse influence table in the model.
                  (reset! (.invertedinfluencehashtable *current-model*) (inverted-method-influence-table)))
                (println "root-class" root "not found in model - can't proceed.")))))))))

(defn load-model
  "Load a model from a file as produced from a pamela build with --json-ir."
  [file root & args]
  (println "Loading " file " root=" root " args=" args)
  (let [raw-json-ir (slurp file)]
    (load-model-from-json-string raw-json-ir root args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interface

(defn set-field-value!
  "Sets the field value of an instance identified by its ID. This is to respond to observations from a plant."
  [id field newvalue]
  (let [object (get-object-from-id id)
        fname (if (string? field) (keyword field) field)]
    (if (not object)
      (if *printdebug*
        (.write *out* (format "%nFailed to find an instance that has the :ID=%s" id)))
      (let [fieldatom (get-field-atom object fname)]
        (if (not fieldatom)
          (do
            (if *printdebug*
              (do
                (.write *out* (format "%nFailed to find field %s in " fname object))
                (describe-rtobject object))))
          (reset! fieldatom newvalue))))))

(defn get-field-value
  "Gets the field value of an instance identified by its ID. This is to respond to observations from a plantto requests from the dispatcher."
  [id field]
  (let [object (get-object-from-id id)
        fname (if (string? field) (keyword field) field)]
    (if (not object)
      (if *printdebug*
        (.write *out* (format "%nFailed to find an instance that has the :ID=%s" id)))
      (let [fieldatom (get-field-atom object fname)]
        (if (not fieldatom)
          (do
            (if *printdebug*
              (do
                (.write *out* (format "%nFailed to find field %s in " fname object))
                (describe-rtobject object))))
          @fieldatom)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Standard propositions about the loaded model

;;; LVAR connectivity

(defn lvars-in-object
  "Scan the fields of an object to find all lvar references."
  [object]
  (into #{}
        (seq
         (remove nil?
                 (map (fn [[name value]]
                        ;;(println "Field: " name)
                        (if (instance? LVar @value) @value nil))
                      @(.fields object))))))

;;; (pprint (lvars-in-object (second (first (get-root-objects)))))

(defn lvar-connectivity-map
  "Iterate over all objects and collect the LVAR's contained in fields"
  []
  (let [;;lvars @(.lvars *current-model*)
        objects @(.objects *current-model*)]
    (into {}
          (seq (remove nil?
                  (map (fn [object]
                         (let [lvar-set (lvars-in-object object)]
                           (if (not (empty? lvar-set))
                             [object lvar-set])))
                       objects))))))

;;; (def cm (lvar-connectivity-map))

(defn object-connectivity-map
  [cm]
  (let [;;lvars @(.lvars *current-model*)
        con (atom {})]
    (doseq [[obj lvs] cm]
      (doseq [lv lvs]
        ;;(println "Adding " (.variable obj) " to " lv)
        (reset! con (into @con {lv (conj (or (get @con lv) #{}) (.variable obj))}))))
    @con))

;;; (def ocm (object-connectivity-map cm))

(defn list-of-connected-objects
  [cm]
  (let [ocm (object-connectivity-map cm)]
    (seq (map (fn [[var connects]] connects) ocm))))

;;; (def lco (list-of-connected-objects cm))

(defn add-connectivity-propositions
  [lco]
  (doseq [interconnected lco]
    (doseq [var interconnected]
      (doseq [ovar interconnected]
        (if (not (= var ovar))
          ;;(println var "connects to" ovar)
          (bs/add-binary-proposition :connects-with var ovar))))))

;;; (add-connectivity-propositions lco)

(defn describe-connectivity-map
  []
  (let [cm (lvar-connectivity-map)]
    (doseq [[object lvars] cm]
      (let [object-name (.variable object)
            lvnames (map (fn [lv] (.name lv)) lvars)]
        (println [object-name lvnames])))))

;;; (describe-connectivity-map)

(defn establish-connectivity-propositions
  []
  (-> (lvar-connectivity-map)
      (list-of-connected-objects)
      (add-connectivity-propositions)))

;;; :is-Part-of propositions

(defn subobjects-in-object
  "Scan the fields of an object to find all object references."
  [object]
  (into #{}
        (seq
         (remove nil?
                 (map (fn [[name value]]
                        ;;(println "Field: " name)
                        (if (instance? RTobject @value) @value nil))
                      @(.fields object))))))

(defn subordinate-object-map
  "Iterate over all objects and collect the LVAR's contained in fields"
  []
  (let [objects @(.objects *current-model*)]
    (into {}
          (seq (remove nil?
                  (map (fn [object]
                         (let [so-set (subobjects-in-object object)]
                           (if (not (empty? so-set))
                             [object so-set])))
                       objects))))))

(def som (subordinate-object-map))

(defn add-part-of-propositions
  [som]
  (doseq [[obj subs] som]
    (let [objname (.variable obj)]
      (doseq [asub subs]
        (let [subname (.variable asub)]
          ;; (println subname "is-part-of " objname)
          (bs/add-binary-proposition :is-part-of subname objname))))))

(defn establish-part-of-propositions
  []
  (-> (subordinate-object-map)
      (add-part-of-propositions)))

(defn describe-connectivity-subordinate-object-map
  []
  (let [som (subordinate-object-map)]
    (doseq [[object subs] som]
      (let [object-name (.variable object)
            subnames (map (fn [sub] (.variable sub)) subs)]
        (println [object-name subnames])))))

;;; (describe-connectivity-subordinate-object-map)

(defn find-objects-of-type
  "Find all instantiated objects of a given type"
  [typename]
  (let [objects @(.objects *current-model*)]
    (remove nil? (map (fn [obj]
                        (if (= (.type obj) typename) obj))
                      (seq objects)))))


(defn nyi
  [msg]
  (throw (Exception. msg)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn resetall
  "Unload everything."
  []
  (unload-model)
  (bs/clear-belief-state)
  nil)

(def maxplandepth 10)
(def numsamples 100)
(def accept-gap-fillers false)

(defn generate-attack-plans
  [ooi]
  (if (and (empty? (find-objects-of-type 'TypicalAttacker))
           (empty? (find-objects-of-type 'TypicalAttacker_Impl)))
    (do (println "TypicalAttacker not found in model - can't proceed.")
        nil)
    (let [attackers (if (empty? (find-objects-of-type 'TypicalAttacker))
                      (find-objects-of-type 'TypicalAttacker_Impl)
                      (find-objects-of-type 'TypicalAttacker))
          attacker (first attackers)
          attackerobjname (.variable attacker)
          rootobject (second (first (get-root-objects)))
          rootobjectname (.variable rootobject)]
      #_(println "Attackers=" attackers
                 "attackerobjname=" attackerobjname
                 "rootobjectname="rootobjectname)
      (bs/monte-carlo-plan-attacks attackerobjname ooi numsamples accept-gap-fillers #{rootobjectname} maxplandepth))))

;;; (def dps (load-desired-properties "/Users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile-guidance.dp.json"))
;;; (def ooi (objects-of-interest dps))

;;; (def attackers (find-objects-of-type 'TypicalAttacker))
;;; (def attacker (.variable (first attackers)))

;;; (println ref " = " (deref-method name rootobject) (if (method-exists name rootobject) "Exists" "Not found"))

;;; (def rootobject (second (first (get-root-objects))))
;;; (def rootobjectname (.variable rootobject))
;;; (validate-desirable-properties dps)
;;; (bs/monte-carlo-plan-attacks attacker ooi 1 #{rootobjectname} maxplandepth)
;;; (generate-attack-plans ooi)








;;; Fin
