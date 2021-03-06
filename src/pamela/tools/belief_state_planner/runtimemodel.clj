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
            [pamela.tools.belief-state-planner.lvarimpl :as lvar]
            [pamela.tools.belief-state-planner.evaluation :as eval]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.prop :as prop]
            [clojure.data.json :as json])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.runtimemodel)

(def ^:dynamic *printdebug* true)
;;(def ^:dynamic *printdebug* false)

(defn unload-model
  "Delete the current model if any."
  []
  ;; For every instantiated object delete its mode variable.
  (doseq [obj (seq @(global/.objects global/*current-model*))]
    (let [pclass (:class obj)
          mode (:mode obj)]
      (if (and (> global/verbosity 2) *printdebug*)
        (.write *out* (format "%nMode of %s: %s" pclass mode)))
      ;; Delete the belief in the objects mode
      (bs/undef-variable mode)
      ))
  (reset! (global/.lvars global/*current-model*) nil)
  (reset! (global/.objects global/*current-model*) nil)
  (reset! (global/.plantmap global/*current-model*) {})
  (reset! (global/.pclasses global/*current-model*) {})
  (reset! (global/.pre-and-post-conditions global/*current-model*) {})
  (reset! (global/.invertedinfluencehashtable global/*current-model*) {})
  (reset! (global/.rootclass global/*current-model*) nil))

(defn resetall
  "Unload everything."
  []
  (unload-model)
  (bs/clear-belief-state)
  nil)

(defn goal-post-conditions
  []
  (second @(global/.pre-and-post-conditions global/*current-model*)))

(defn inverted-influence-table
  []
  @(global/.invertedinfluencehashtable global/*current-model*))

(defn get-root-class-name
  []
  @(global/.rootclass global/*current-model*))


(defn get-root-fields
  []
  (let [root (second (first (global/get-root-objects)))
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
                                           (if (global/RTobject? @obj)
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

(defn describe-current-model
  "Print out a description of the currently loaded model."
  []
  (let [lvars @(global/.lvars global/*current-model*)
        rootclass @(global/.rootclass global/*current-model*)
        objects @(global/.objects global/*current-model*)
        [pre post] @(global/.pre-and-post-conditions global/*current-model*)
        iiht @(global/.invertedinfluencehashtable global/*current-model*)]
    (.write *out* (format "%nCurrent model:%n%nLVARS:%n"))
    (doseq [lvar (seq lvars)]
      (lvar/describe-lvar lvar))
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
    (doseq [[k v] @(global/.plantmap global/*current-model*)]
      (.write *out* (format "%nPlant ID: %s = %s" k v)))))

(defn in?
  "true if coll contains elm"
  [coll elm]
  (some #(= elm %) coll))

(defn objects-matching
  [apredicate-on-object]
  (let [all-objects @(global/.objects global/*current-model*)]
    (println "test on first object: " (if (apredicate-on-object (first all-objects)) "YES!"))
    (filter apredicate-on-object all-objects)))

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
  (global/.pre-and-post-conditions global/*current-model*))

(defn controllable-object?
  "This is a test that the object in question is controllable by the planner. REWRITE+++"
  [id rtobj]
  (let [idname (str id)]
    (Character/isUpperCase (first idname))))

(defn get-controllable-objects
  "Returns a sequence of all of the controllable objects."
  []
  (let [objects @(global/.plantmap global/*current-model*)]
    (remove nil? (map (fn [[id rtobj]]
                        (if (controllable-object? id rtobj) [id rtobj] nil))
                      objects))))

(defn get-class-by-name
  [name]
  (let [current-classes (into {} @(global/.pclasses global/*current-model*))
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
  (let [r-objects (global/get-root-objects)]
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
      (:equal :notequal :same :notsame :gt :ge :lt :le)
      (cond (or (and (vector? (nth condition 1))
                     (or (= (first (nth condition 1)) :arg) (= (first (nth condition 1)) :field))
                     (vector? (nth condition 2)) (= (first (nth condition 2)) :mode-of))
                (and (vector? (nth condition 2))
                     (or (= (first (nth condition 2)) :arg) (= (first (nth condition 2)) :field))
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

      (:and :or :implies) (apply concat (map (fn [arg] (compile-influence arg)) (rest condition)))

      :mode-of (list [:mode])

      :not (compile-influence (nth condition 1))
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
                                         [[@(global/.rootclass global/*current-model*) effect] pmeth])) ; +++was pcls
                                     effects))
                              inf-table))]
    (group-by-first-equal eff-table)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;; was (defn make-arglist
;;; was   "Construct an arglist from an initial field constructor"
;;; was   [pcarglist args instance]
;;; was   (if (= (count pcarglist) 0)
;;; was     nil
;;; was     (let [alist (seq (map #(vector %1 (eval/eval-arg %2 instance)) (seq pcarglist) (seq args)))]
;;; was       #_(.write *out* (format "%n In make-arglist: Arglist=%s Args=%s result=%s %n" pcarglist args alist))
;;; was       alist)))

;; (defn make-arglist ;; +++ not used
;;   "Construct an arglist from an initial field constructor"
;;   [pcarglist args instance]
;;   (if (= (count pcarglist) 0)
;;     nil
;;     (let [alist (seq (map #(vector %1 (eval/eval-arg %2 instance)) (seq pcarglist) (seq args)))]
;;       #_(.write *out* (format "%n In make-arglist: Arglist=%s Args=%s result=%s %n" pcarglist args alist))
;;       alist)))

;; (defn make-lvar  ;; +++ not used
;;   "Construct an lvar object"
;;   [instance field aname]
;;   (let [varname (gensym (:name aname))]
;;     (bs/add-variable varname (:name aname) nil)
;;     {:lvar (:name aname) :value varname :instance instance :field field}))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Evaluators

(declare find-objects-of-name)

(defn clone-object
  [instance-name object]
  (let [id (global/RTobject-id object)
        cname (global/RTobject-type object)
        obj-field-map (global/RTobject-fields object)
        field-map (into {} (map (fn [[k v]] [k (atom @v)]) @obj-field-map))
        clone (global/make-object instance-name cname field-map id)
        pclass (get-class-by-name cname)
        modes (seq (get pclass :modes))]
    (bs/add-variable instance-name cname (map first modes)) ; create variable
    (bs/add-binary-proposition :is-a instance-name (str cname))
    (global/add-object clone)
    clone))

(defn delete-object
  [object]
  (let [id (global/RTobject-id object)
        ;;cname (global/RTobject-type object)
        obj-field-map (global/RTobject-fields object)
        var (global/RTobject-variable object)]
    (global/remove-object object)              ; Remove the object from the list of objects
    (bs/undef-variable var))            ; Remove the belief in the variable
  :deleted)

(defn assert-propositions
  [props]
  (if (> global/verbosity 0) (println "Installing propositions"))
  (if (> global/verbosity 2) (pprint props))
  (doseq [[prop a1 a2] (rest props)]
    (bs/add-binary-proposition prop a1 a2))
  (if (> global/verbosity 2) (bs/print-propositions)))

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
    (global/add-pclasses spam)
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
                  _ (if (> global/verbosity 3) (pprint root))
                  sroot [rootsym []]
                  ;; _ (pprint sroot)
                  root-class (irx/get-spamela-class-from-ir ir sroot)
                  ;; _ (pprint root-class)
                  root-methods (get root-class :methods)
                  _ (if (> global/verbosity 3) (pprint (prop/prop-readable-form root-methods)))
                  goal-method (last root-methods) ; +++ was first
                  _ (if (> global/verbosity 3) (pprint  (prop/prop-readable-form goal-method)))
                  _ (if (> global/verbosity 3) (println :pre (prop/prop-readable-form (irx/.prec goal-method))
                                                        :post (prop/prop-readable-form (irx/.postc goal-method))))
                  pre-and-post (if (and root-class goal-method)
                                 [[rootsym (irx/.prec goal-method)] [rootsym (irx/.postc goal-method)]])]
              (if root-class
                (do
                  (reset! (global/.rootclass global/*current-model*) rootsym)
                  (global/add-preandpost pre-and-post)
                  #_(.write *out* (format "%nRoot class %s, found %s" sroot
                                          (with-out-str (pprint root-class))))
                  (eval/instantiate-pclass nil (str "/" (first sroot)) (first sroot) spam root-class nil args "root" "root-part")
                  ;; Now establish the inverse influence table in the model.
                  (reset! (global/.invertedinfluencehashtable global/*current-model*) (inverted-method-influence-table)))
                (println "root-class" root "not found in model - can't proceed.")))))))))

(defn load-model-from-json-string
  [json-string root args]
  (let [ir (irx/read-ir-from-json-string json-string)]
    (load-model-from-ir ir root args)))

(defn load-model
  "Load a model from a file as produced from a pamela build with --json-ir."
  [file root & args]
  (if (> global/verbosity 0) (println "Loading " file " root=" root " args=" args))
  (let [raw-json-ir (slurp file)]
    (load-model-from-json-string raw-json-ir root args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interface

(defn set-field-value!
  "Sets the field value of an instance identified by its ID. This is to respond to observations from a plant."
  [id field newvalue]
  (let [object (global/get-object-from-id id)
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
  (let [object (global/get-object-from-id id)
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
                        (if (lvar/is-lvar? @value) @value nil))
                      @(.fields object))))))

;;; (pprint (lvars-in-object (second (first (global/get-root-objects)))))

(defn lvar-connectivity-map
  "Iterate over all objects and collect the LVAR's contained in fields"
  []
  (let [objects @(global/.objects global/*current-model*)]
    (into {}
          (seq (remove nil?
                  (map (fn [object]
                         (let [lvar-set (lvars-in-object object)]
                           (if (not (empty? lvar-set))
                             [object lvar-set])))
                       objects))))))

;;; Find all objects that contain a specific LVAR

(defn objects-containing-lvar
  "Iterate over all objects and collect the LVAR's contained in fields that match anlvar"
  [anlvar]
  (let [objects @(global/.objects global/*current-model*)
        objconnlvar (into []
                          (remove nil?
                                  (map (fn [object]
                                         (let [lvar-set (lvars-in-object object)]
                                           (if (and (not (empty? lvar-set))
                                                    (some #{anlvar} lvar-set))
                                             object)))
                                       objects)))]
    objconnlvar))

;;; (def cm (lvar-connectivity-map))

(defn object-connectivity-map
  [cm]
  (let [;;lvars @(global/.lvars global/*current-model*)
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

(defn find-objects-of-types
  "Find all instantiated objects belong to any of a seq of types"
  [typenames]
  (let [typeset (set typenames)
        objects @(global/.objects global/*current-model*)]
    (remove nil? (map (fn [obj]
                        (if (some typeset [(.type obj)]) obj))
                      objects))))

(defn add-connectivity-propositions
  [lco root pred]
  (let [rootobj (if root (first (eval/find-objects-of-type (symbol root))))
        rootvar (if rootobj (.variable rootobj))]
    ;; (println "rootvar=" rootvar "root=" root)
    (doseq [interconnected lco]
      (doseq [var interconnected]
        (doseq [ovar interconnected]
          (if (and (not (= var ovar))
                   (not (= var  rootvar))
                   (not (= ovar rootvar))
                   (or (not pred) (pred var ovar)))
            (bs/add-binary-proposition :connects-with var ovar)))))))

(defn add-connectivity-propositions-unidirectional
  [lco root pred]
  (let [done (atom #{})
        rootobj (if root (first (eval/find-objects-of-type (symbol root))))
        rootvar (if rootobj (.variable rootobj))]
    ;; (println "rootvar=" rootvar)
    (doseq [interconnected lco]
      (doseq [var interconnected]
        (doseq [ovar interconnected]
          (if (and (not (= var ovar))
                   (not (= var  rootvar))
                   (not (= ovar rootvar))
                   (empty? (set/intersection @done (set [[var ovar][ovar var]])))
                   (or (not pred) (pred var ovar)))
            (do
              (bs/add-binary-proposition :connects-with var ovar)
              (reset! done (set/union @done (set [[var ovar][ovar var]]))))))))))

;;; (add-connectivity-propositions lco)

(defn describe-connectivity-map
  []
  (let [cm (lvar-connectivity-map)]
    (doseq [[object lvars] cm]
      (let [object-name (.variable object)
            lvnames (map (fn [lv] (lvar/.name lv)) lvars)]
        (println [object-name lvnames])))))

;;; (describe-connectivity-map)

(defn establish-connectivity-propositions
  [root & [pred]]
  (-> (lvar-connectivity-map)
      (list-of-connected-objects)
      (add-connectivity-propositions root pred)))

(defn establish-unidirectional-connectivity-propositions
  [root & [pred]]
  (-> (lvar-connectivity-map)
      (list-of-connected-objects)
      (add-connectivity-propositions-unidirectional root pred)))

;;; :is-Part-of propositions

(defn subobjects-in-object
  "Scan the fields of an object to find all object references."
  [object]
  (into #{}
        (seq
         (remove nil?
                 (map (fn [[name value]]
                        ;;(println "Field: " name)
                        (if (global/RTobject? @value) @value nil))
                      @(.fields object))))))

(defn subordinate-object-map
  "Iterate over all objects and collect the LVAR's contained in fields"
  []
  (let [objects @(global/.objects global/*current-model*)]
    (into {}
          (seq (remove nil?
                  (map (fn [object]
                         (let [so-set (subobjects-in-object object)]
                           (if (not (empty? so-set))
                             [object so-set])))
                       objects))))))

(def som (subordinate-object-map))

(defn add-part-of-propositions
  [som root pred]
  (doseq [[obj subs] som]
    (let [objname (.variable obj)
          rootobj (symbol root)]
      (doseq [asub subs]
        (let [subname (.variable asub)
              proposition (if (= (.type obj) rootobj) :has-root :is-part-of)]
          ;; (println "In add-part-of-propositions: " root (.type obj) subname proposition objname)
          (if (or (not pred) (pred objname subname))
            (bs/add-binary-proposition proposition subname objname)))))))

(defn establish-part-of-propositions
  [root & [pred]]
  (-> (subordinate-object-map)
      (add-part-of-propositions root pred)))

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
  (let [objects (eval/find-objects-of-type object-type)]
    (if (not (empty? objects))
      (let [;; - (println "Found objects : " objects)
            fieldat (get-field-atom (first objects) field)]
        (if fieldat
          (let [field-val @fieldat]
            (if field-val (.type field-val)))
          (println "Field " field " does not exist in " (first objects))))
      (do (println "No objects of type " object-type "were found.") nil))))

;;; Does this really belong here? Maybe move it to DCRYPPS
;;; It's use seems a little specialized -- not sure though.
(defn find-name-of-field-objects
  [object-type field]
  (println "In find-name-of-field-object with object-type=" object-type "and field=" field)
  (let [objects (eval/find-objects-of-type object-type)]
    (if (not (empty? objects))
      (let [;; _ (println "Found objects : " objects)
            fieldat (get-field-atom (first objects) field)]
        (println "In find-name-of-field-objects with fieldat=" (prop/prop-readable-form fieldat))
        (cond
          (and fieldat
               (instance? clojure.lang.Atom fieldat)
               (global/RTobject? @fieldat))
          [(global/RTobject-variable @fieldat)]

          (and fieldat
               (instance? clojure.lang.Atom fieldat)
               (lvar/is-lvar? @fieldat))
          (let [lvconnobjs (objects-containing-lvar @fieldat)]
            (println "lvconnobjs=" (prop/prop-readable-form lvconnobjs))
            (if (empty? lvconnobjs)
              (let [objvars [(global/RTobject-variable (first objects))]]
                (println "result is:" objvars)
                objvars) ; Forget the field, the object is implicated +++ probably should obsolete this case
              (let [objvars (map global/RTobject-variable lvconnobjs)]
                (println "result is:" objvars)
                objvars)))

          (nil? fieldat)
          nil

          :otherwise
          (println "Field " field " does not exist in " (first objects))))
      (do (println "No objects of type " object-type "were found.") nil))))

(defn nyi
  [msg]
  (throw (Exception. msg)))


;;; Fin
