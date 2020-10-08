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
            [clojure.set :as set]
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

(defrecord RTobject [variable type fields id])

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

(defrecord LVar [name binding boundp])

(defn LVar?
  [x]
  (instance? LVar x))

(def ^:dynamic *printdebug* true)
;;(def ^:dynamic *printdebug* false)
(def ^:dynamic verbosity 0) ; 0

(defn set-verbosity
  [n]
  (def ^:dynamic verbosity n))

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
      (if (and (> verbosity 2) *printdebug*)
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

(defn resetall
  "Unload everything."
  []
  (unload-model)
  (bs/clear-belief-state)
  nil)

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

 (defn get-root-field-value
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

(defn remove-object
  "Remove an object from the current model."
  [object]
  (reset! (.objects *current-model*) (remove #{object} @(.objects *current-model*))))

(defn add-lvar
  "Add an lvar to the current model."
  [lv]
  ;;  (if (not (in? (.lvars *current-model*) lv))
  (reset! (.lvars *current-model*) (cons lv @(.lvars *current-model*)))
  ) ;;)

(defn add-pclasses
  "Add an pclasses from a loaded model file."
  [pcs]
  (if (and (> verbosity 1) *printdebug*)
    (do (println "adding spam:\n")
        (pprint pcs)))
  (reset! (.pclasses *current-model*) pcs)) ;+++ unfinished, thsi needs to merge with whats already there

(defn add-preandpost
  "Add a preandpost condition vector from a loaded model file."
  [ppcs]
  (if (and (> verbosity 2) *printdebug*)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Lvar implementation

(def planbindset nil)

(defn make-lvar
  [name]
  (let [lv (LVar. name (atom nil) (atom :unbound))]
    (add-lvar lv)
    lv))

(defn is-lvar?
  [thing]
  (instance? LVar thing))

(defn is-bound-lvar?
  [thing]
  (not (= @(.boundp thing) :unbound)))

(defn is-unbound-lvar?
  [thing]
  (= @(.boundp thing) :unbound))

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
      (if planbindset (reset! planbindset (conj @planbindset lv)))
      (reset! (.boundp lv) :bound)
      (reset! (.binding lv) (deref-lvar nval)))
    (let [boundto (deref-lvar lv)]
      (if (instance? LVar boundto)
        (bind-lvar boundto nval)
        (= boundto (deref-lvar nval))))))

(defn unbind-lvar
  [lv]
  (reset! (.boundp lv) :unbound)
  (reset! (.binding lv) nil))

;;; Start tracking LV bind operations

(defn unbind-planbind-set
  []
  (if planbindset
    (do
      (doseq [lvar @planbindset]
        (if (> verbosity 1) (println "Unbinding LVAR " (.name lvar)))
        (unbind-lvar lvar)))))

(defn start-plan-bind-set
  []
  (if (> verbosity 1) (println "Starting to collect LVAR bindings"))
  (if (not (= planbindset nil)) (unbind-planbind-set))
  (def planbindset (atom #{})))

(defn stop-plan-bind-set
  []
  (if (> verbosity 1) (println "Stopping collecting LVAR bindings"))
  (unbind-planbind-set)
  (def planbindset nil))

;;; (def x (make-lvar "x"))
;;; x
;;; (start-plan-bind-set)
;;; planbindset
;;; (bind-lvar x 42)
;;; x
;;; planbindset
;;; (stop-plan-bind-set)
;;; x
;;; planbindset

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
      (:equal :gt :ge :lt :le)
                   (cond (or (and (vector? (nth condition 1)) (= (first (nth condition 1)) :arg)
                                  (vector? (nth condition 2)) (= (first (nth condition 2)) :mode-of))
                             (and (vector? (nth condition 2)) (= (first (nth condition 2)) :arg)
                                  (vector? (nth condition 1)) (= (first (nth condition 1)) :mode-of)))
                         (list [:arg-mode])

                         (and (= (first (nth condition 1)) :field))
                         (list (nth condition 1))

                         (and (vector? (nth condition 2)) (= (first (nth condition 2)) :field))
                         (list (nth condition 2))

                         (and (vector? (nth condition 1)) (= (first (nth condition 1)) :arg-field))
                         (list (nth condition 1))

                         (and (vector? (nth condition 2)) (= (first (nth condition 2)) :arg-field))
                         (list (nth condition 2))

                         :else
                         (list (extract-referents condition)))

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
                                       (cond
                                         (and (not (keyword? effect))
                                              (or
                                               (= (first effect) :arg-mode)
                                               (= (first effect) :arg-field)))
                                         [[:any effect] pmeth]

                                         :otherwise
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
    (if (> verbosity 3) (println "initial-mode-of modes=" modes " emodes =" emodes " initial=" initial))
    (or initial (first (first modes)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Evaluators

(declare instantiate-pclass)
(declare deref-field)
(declare find-objects-of-name)

(defn instantiation-error
  [astring]
  (throw (Throwable. (str "Instantiation error: " astring))))

(defn get-likely-value
  [pdf threshold]
  (let [values (keys pdf)
        numvals (count values)]
    (if (> verbosity 3) (println "In get-likely-value pdf=" pdf "threshold=" threshold "values=" values "numvals=" numvals))
    (if (empty? pdf)
      :null
      (case numvals
        0 :null

        1 (first values)
        (let [best (apply max-key val pdf)]
          (if (>= (second best) threshold)
            (first best)
            :null))

        :unknown))))

(defn maybe-get-named-object
  [val]
  (let [res (cond (string? val) ; +++ got to undo this string names and use symbols instead
                  (let [var (first (find-objects-of-name val))]
                    (when (nil? var)
                      (when (> verbosity 3)
                        (println "Didn't find object named" val)
                        (doseq [anobj @(.objects *current-model*)]
                          (println (.variable anobj)))))
                    (or var val))

                  :otherwise val)]
    (if (and (> verbosity 3) (not (= val res)))
      (println "maybe-get-named-object var=" val "val=" res))
    res))

(defn evaluate
  "Evaluate an expression in the current belief state with args as provided."
  [wrtobject path expn class-bindings method-bindings cspam spam]
  #_(println "\nIn evaluate with expn=" expn
             " path=" path
             " class-bindings=" class-bindings
             " method-bindings=" method-bindings)
  ;; (pprint spam)
  (case expn
    :true true
    :false false
    (if (or (string? expn) (number? expn) (symbol? expn) (keyword? expn))
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
              :mode-ref
              (get expn :mode)

              (do (irx/error "Unknown form in Evaluate: " expn)
                  expn)))
          (irx/error "In evaluate: unexpected expression found: " expn))
        (case (first expn)
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
          :value (let [val (second expn)]
                   (if (not (instance? RTobject val))
                     val
                     (let [variable (.variable val) ; +++ avoid duplication of this idiom
                           pdf (bs/get-belief-distribution-in-variable variable)]
                       (if (> verbosity 3) (println "variable=" variable "pdf=" pdf))
                       (get-likely-value pdf 0.8))))
          :thunk (evaluate (nth expn 2) path (second expn) class-bindings method-bindings cspam spam)
          :or (some #(evaluate wrtobject path % class-bindings method-bindings cspam spam) (rest expn))
          :and (every? #(evaluate wrtobject path % class-bindings method-bindings cspam spam) (rest expn))
          ;; :or (if (= (count (rest expn)) 1)
          ;;       (evaluate wrtobject path (second expn) class-bindings method-bindings cspam spam)
          ;;       :true) ;+++ this is not finished +++ only the trivial case is implemented
          :arg nil                            ; method arg NYI
          :class-arg (let [res (get class-bindings (second expn))]
                       (if (and (not (number? res)) (not (symbol? res)) (not (keyword? res)) (empty? res))
                         (irx/error "In evaluate with " expn "class-bindings=" class-bindings "res=" res))
                       res)
          :field-ref (do (irx/error "UNEXPECTED: Found a field ref: " expn) nil)
          :field (let [value (deref-field (rest expn) wrtobject :normal)]
                   (if (not (instance? RTobject value))
                     value
                     (let [variable (.variable value)
                           pdf (bs/get-belief-distribution-in-variable variable)]
                       (if (> verbosity 3) (println "variable=" variable "pdf=" pdf))
                       (get-likely-value pdf 0.8))))  ; +++ where did 0.8 come from!!!

          :arg-field (let [[object & field] (rest expn)
                           - (if (> verbosity 2) (println ":arg-field object= " object "field=" field "expn=" expn))
                           obj (cond
                                 (RTobject? object)
                                 object

                                 (= (first object) :value)
                                 (second object)

                                 :otherwise
                                 (deref-field (rest object) #_wrtobject (second (first (get-root-objects))) :normal)) ; Force caller to be root+++?
                           - (if (> verbosity 2) (println ":arg-field obj= " obj))
                           value (maybe-get-named-object (deref-field field obj :normal))
                           ] ; +++ handle multilevel case
                         (if (not (instance? RTobject value))
                           value
                           (let [variable (.variable value) ; +++ avoid duplication of this idiom
                                 pdf (bs/get-belief-distribution-in-variable variable)]
                             (if (> verbosity 3) (println "variable=" variable "pdf=" pdf))
                             (get-likely-value pdf 0.8))))

          :mode-of (last expn)
          :make-lvar (make-lvar (second expn))
          :function-call (do
                           (println "evaluate: :function-call")
                           (pprint expn)
                           true)
          (do
            (irx/error "Unknown case: " expn)
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
              :lvar (irx/error "evaluate-reference: lvar constructor found where it wasn't expected: " expn)
              :mode-ref expn
              (do (irx/error "evaluate-reference: Unknown form in Evaluate: " expn)
                  expn)))
          (irx/error "evaluate-reference: unexpected expression: expn"))
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
                   (if (not (instance? RTobject value))
                     value
                     [:value value]))

          :arg-field (let [[object & field] (rest expn)
                           - (if (> verbosity 2) (println ":arg-field object= " object "field=" field "expn=" expn))
                           obj (cond
                                   (RTobject? object)
                                   object

                                   (and (vector? object) (= (first object) :value))
                                   (second object)

                                   (and (vector? object) (= (first object) :arg-field))
                                   (evaluate-reference wrtobject object class-bindings method-bindings cspam spam)

                                   :otherwise
                                   (deref-field (rest object) (second (first (get-root-objects))) :reference)) ; Force caller to be root+++?
                           - (if (> verbosity 2) (println ":arg-field obj= " obj))
                           value (deref-field field obj :reference)] ; +++ handle multilevel case
                         (if (not (instance? RTobject value))
                           value
                           [:value value]))

          :mode-of [:value (last expn)]

          :value expn

          :function-call (irx/error "Unknown case: " expn))))))

(defn maybe-deref
  [thing mode]
  (let [derefedthing
        (if (= (type thing) clojure.lang.Atom)
          @thing
          thing)
        deboundthing
        (if (and (not (= mode :reference)) (is-lvar? derefedthing) (is-bound-lvar? derefedthing))
          (deref-lvar derefedthing)
          derefedthing)]
    deboundthing))

(defn deref-field
  [namelist wrtobject mode]
  (if (> verbosity 2)
    (println "deref-field: " namelist "wrt-object=" (if (instance? RTobject wrtobject) (.variable wrtobject) [:oops wrtobject]) "mode=" mode))
  (cond ;;RTobject? (first namelist)) ; Obsolete
        ;;(first namelist)

        (and (vector? (first namelist)) (= (first (first namelist)) :value))
        (second (first namelist))

        (vector? wrtobject)
        (do (irx/error "dereference failed on bad wrtobject=" wrtobject)
            [:not-found namelist])

        (empty? wrtobject)
        (do
          (irx/error "trying to dereference " namelist "with null wrtobject!")
          [:not-found namelist])

        :otherwise
        (let [fields (.fields wrtobject)
              ;; - (println "***!!! fields = " @fields)
              match (get @fields (first namelist) )
              ;; - (println "***!!! found match for" (first namelist)  " = " match)
              remaining (rest namelist)]
          (if (empty? remaining)
            (do
              ;; (println "***!!! dereferenced " (first namelist) "=" match)
              (if (= match nil)
                (irx/error "DEREF ERROR: [:not-found" namelist ":in" wrtobject "]")
                (maybe-deref match mode)))
            (do
              (if (not (= match nil))
                (do
                  ;; (println "***!!! recursive dereference with object=" @match)
                  (deref-field remaining @match mode))
                [:not-found namelist :in wrtobject]))))))

(defn field-exists
  [names wrtobject]
  (let [result (deref-field names wrtobject :normal)]
    (not (and (vector? result) (= (count result) 2) (= (first result) :not-found)))))

(defn lookup-class
  [cname]
  (let [pclass-defs (into {} @(.pclasses *current-model*))]
    (get pclass-defs cname)))

(defn deref-method
  [names wrtobject]
  (let [object (if (= (count names) 1)
                 wrtobject
                 (deref-field (take (- (count names) 1) names) wrtobject :normal))]
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

(defn clone-object
  [instance-name object]
  (let [id (RTobject-id object)
        cname (RTobject-type object)
        obj-field-map (RTobject-fields object)
        field-map (into {} (map (fn [[k v]] [k (atom @v)]) @obj-field-map))
        clone (RTobject. instance-name cname (atom field-map) id)
        pclass (get-class-by-name cname)
        modes (seq (get pclass :modes))]
    (bs/add-variable instance-name cname (map first modes)) ; create variable
    (bs/add-binary-proposition :is-a instance-name (str cname))
    (add-object clone)
    clone))

(defn delete-object
  [object]
  (let [id (RTobject-id object)
        ;;cname (RTobject-type object)
        obj-field-map (RTobject-fields object)
        var (RTobject-variable object)]
    (remove-object object)              ; Remove the object from the list of objects
    (bs/undef-variable var))            ; Remove the belief in the variable
  :deleted)

(defn assert-propositions
  [props]
  (if (> verbosity 0) (println "Installing propositions"))
  (if (> verbosity 2) (pprint props))
  (doseq [[prop a1 a2] (rest props)]
    (bs/add-binary-proposition prop a1 a2))
  (if (> verbosity 2) (bs/print-propositions)))

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
        newObject (RTobject. instance-name cname (atom nil) id)]
    (if (and (> verbosity 1) *printdebug*)
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
                  (reset! valatom (evaluate newObject (str instance-name "." fname) initial argmap nil class-spam spam)))))))
        ;; (println "Satisfied=" @satisfied "touched=" @touched "field-vector:")
        ;; (pprint field-vector)
        )
      ;; (println "Here are the fields that we found: " fields)
      newObject)))


(defn get-field-atom
  "Find the atom represented by the specified field name in the RTobject provided."
  [object field]
  (let [fields @(.fields object)
        fieldatom (if fields (get fields field))]
    #_(if fieldatom
      (.write *out* (format "%nFound field %s = %s !!!%n" field fields))
      (.write *out* (format "%nField %s not found in %s !!!%n" field fields)))
    fieldatom))

(defn load-model-from-ir
  [ir root args]
  (let [spam (irx/json-ir-to-spamela ir false)]
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
                  _ (if (> verbosity 3) (pprint root))
                  sroot [rootsym []]
                  ;; _ (pprint sroot)
                  root-class (irx/get-spamela-class-from-ir ir sroot)
                  ;; _ (pprint root-class)
                  root-methods (get root-class :methods)
                  _ (if (> verbosity 3) (pprint root-methods))
                  goal-method (last root-methods) ; +++ was first
                  _ (if (> verbosity 3) (pprint  goal-method))
                  _ (if (> verbosity 3) (println :pre (irx/.prec goal-method) :post (irx/.postc goal-method)))
                  pre-and-post (if (and root-class goal-method)
                                 [[rootsym (irx/.prec goal-method)] [rootsym (irx/.postc goal-method)]])]
              (if root-class
                (do
                  (reset! (.rootclass *current-model*) rootsym)
                  (add-preandpost pre-and-post)
                  #_(.write *out* (format "%nRoot class %s, found %s" sroot
                                          (with-out-str (pprint root-class))))
                  (instantiate-pclass nil (str "/" (first sroot)) (first sroot) spam root-class nil args "root" "root-part")
                  ;; Now establish the inverse influence table in the model.
                  (reset! (.invertedinfluencehashtable *current-model*) (inverted-method-influence-table)))
                (println "root-class" root "not found in model - can't proceed.")))))))))

(defn load-model-from-json-string
  [json-string root args]
  (let [ir (irx/read-ir-from-json-string json-string)]
    (load-model-from-ir ir root args)))

(defn load-model
  "Load a model from a file as produced from a pamela build with --json-ir."
  [file root & args]
  (if (> verbosity 0) (println "Loading " file " root=" root " args=" args))
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
        ;;(println "Adding " (.variable obj) " to " lv) ;+++ comment me out
        (reset! con (into @con {lv (conj (or (get @con lv) #{}) (.variable obj))}))))
    @con))

;;; (def ocm (object-connectivity-map cm))

(defn list-of-connected-objects
  [cm]
  (let [ocm (object-connectivity-map cm)]
    (seq (map (fn [[var connects]] connects) ocm))))

;;; (def lco (list-of-connected-objects cm))

;;; Should have made objects a map
(defn find-objects-of-name
  "Find all instantiated objects of a given type"
  [vname]
  (let [objects @(.objects *current-model*)]
    (remove nil? (map (fn [obj]
                        (if (= (.variable obj) vname) obj))
                      (seq objects)))))

(defn find-objects-of-type
  "Find all instantiated objects of a given type"
  [typename]
  (let [objects @(.objects *current-model*)]
    (remove nil? (map (fn [obj]
                        (if (= (.type obj) typename) obj))
                      (seq objects)))))

(defn find-objects-of-types
  "Find all instantiated objects belong to any of a seq of types"
  [typenames]
  (let [typeset (set typenames)
        objects @(.objects *current-model*)]
    (remove nil? (map (fn [obj]
                        (if (some typeset [(.type obj)]) obj))
                      objects))))

(defn add-connectivity-propositions
  [lco root]
  (let [rootobj (if root (first (find-objects-of-type (symbol root))))
        rootvar (if rootobj (.variable rootobj))]
    ;; (println "rootvar=" rootvar "root=" root)
    (doseq [interconnected lco]
      (doseq [var interconnected]
        (doseq [ovar interconnected]
          (if (and (not (= var ovar))
                   (not (= var  rootvar))
                   (not (= ovar rootvar)))
            (bs/add-binary-proposition :connects-with var ovar)))))))

(defn add-connectivity-propositions-unidirectional
  [lco root]
  (let [done (atom #{})
        rootobj (if root (first (find-objects-of-type (symbol root))))
        rootvar (if rootobj (.variable rootobj))]
    ;; (println "rootvar=" rootvar)
    (doseq [interconnected lco]
      (doseq [var interconnected]
        (doseq [ovar interconnected]
          (if (and (not (= var ovar))
                   (not (= var  rootvar))
                   (not (= ovar rootvar))
                   (empty? (set/intersection @done (set [[var ovar][ovar var]]))))
            (do
              (bs/add-binary-proposition :connects-with var ovar)
              (reset! done (set/union @done (set [[var ovar][ovar var]]))))))))))

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
  [root]
  (-> (lvar-connectivity-map)
      (list-of-connected-objects)
      (add-connectivity-propositions root)))

(defn establish-unidirectional-connectivity-propositions
  [root]
  (-> (lvar-connectivity-map)
      (list-of-connected-objects)
      (add-connectivity-propositions-unidirectional root)))

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
  [som root]
  (doseq [[obj subs] som]
    (let [objname (.variable obj)
          rootobj (symbol root)]
      (doseq [asub subs]
        (let [subname (.variable asub)
              proposition (if (= (.type obj) rootobj) :has-root :is-part-of)]
          ;; (println "In add-part-of-propositions: " root (.type obj) subname proposition objname)
          (bs/add-binary-proposition proposition subname objname))))))

(defn establish-part-of-propositions
  [root]
  (-> (subordinate-object-map)
      (add-part-of-propositions root)))

(defn describe-connectivity-subordinate-object-map
  []
  (let [som (subordinate-object-map)]
    (doseq [[object subs] som]
      (let [object-name (.variable object)
            subnames (map (fn [sub] (.variable sub)) subs)]
        (println [object-name subnames])))))

;;; (describe-connectivity-subordinate-object-map)

(defn find-type-of-field
  [object-type field]
  (let [objects (find-objects-of-type object-type)]
    (if (not (empty? objects))
      (let [;; - (println "Found objects : " objects)
            fieldat (get-field-atom (first objects) field)]
        (if fieldat
          (let [field-val @fieldat]
            (if field-val (.type field-val)))
          (println "Field " field " does not exist in " (first objects))))
      (do (println "No objects of type " object-type "were found.") nil))))

(defn find-name-of-field-object
  [object-type field]
  (let [objects (find-objects-of-type object-type)]
    (if (not (empty? objects))
      (let [;; - (println "Found objects : " objects)
            fieldat (get-field-atom (first objects) field)]
        (if fieldat
          (let [field-val @fieldat]
            (if field-val (.variable field-val)))
          (println "Field " field " does not exist in " (first objects))))
      (do (println "No objects of type " object-type "were found.") nil))))

(defn nyi
  [msg]
  (throw (Exception. msg)))


;;; Fin
