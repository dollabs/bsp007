;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.ir-extraction
  "Intermediate Representation Extraction"
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
            [clojure.set :as set]
            [pamela.tools.belief-state-planner.expressions :as dxp]
            )
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.ir-extraction)

(def ^:dynamic pamela-model nil)
(def ^:dynamic outfile nil)
(def ^:dynamic verbosity 0)
(def ^:dynamic inrepl false)
;;;(def ^:dynamic inrepl true)

(defn set-verbosity
  [n]
  (def ^:dynamic verbosity n))

(defn read-ir-file [pathstring]
  (read-string (slurp pathstring)))

;;;(def switchandbulb-edn "/Users/paulr/checkouts/DOLL/projects/PAMELA/samples/SwitchAndBulbTestbed/switchandbulb.model.edn")
;;;(def biased-coin-edn "/Users/paulr/checkouts/DOLL/projects/PAMELA/beliefstate/biased-coin.model.edn")
;;;(def demo-mar-2017-edn "/Users/paulr/checkouts/DOLL/projects/dance/code/demo-march-2017/pamela/demo-mar-2017.ir.edn")

(def ^:dynamic *testir* nil)

(defn readiniffordebugging [file]
  (def ^:dynamic *testir*  (read-ir-file file)))

;;; (readiniffordebugging biased-coin-edn)
;;; (readiniffordebugging switchandbulb-edn)
;;; (readiniffordebugging switchandbulb-edn)

(defn setirfortesting [ir]
  (def ^:dynamic *testir* ir))

(defn break
  [& message]
  (print "BREAK: ")
  (apply println message)
  (if inrepl
    (do
      (println "(type y to continue, ^C ^C to abort)")
      (case (let [answer (read) - (println answer)] answer)
        y true
        (recur message)))))

(defn error
  [& message]
  (print "ERROR: ")
  (apply println message)
  (if inrepl
    (do
      (println "(type y to continue anyway, ^C ^C to abort)")
      (case (let [answer (read) - (println answer)] answer)
        y true
        (/ 1 0)  #_(clojure.stacktrace/print-stack-trace (Exception. "Error"))
        (recur message)))))

;;; (error "This is a test" 42 "error message")

(defn unencode-ir-strings
  "Unencode string/symbol/keyword encoded as readable strings"
  [ir]
  (cond (string? ir) (read-string ir)
        ;; Recursive data structures
        (list? ir) (map (fn [sir] (unencode-ir-strings sir)) ir)
        (vector? ir) (seq (map (fn [sir] (unencode-ir-strings sir)) ir))
        (set? ir) (set (map (fn [sir] (unencode-ir-strings sir)) ir))
        (map? ir) (into {} (map (fn [[key val]] {(unencode-ir-strings key) (unencode-ir-strings val)}) ir))
        :else ir))                                ; All other cases remain unchanged.

(defn read-ir-from-json-string
  "Given a JSON IR string for a pamela model (compiled with --json-ir) unencodes the strings to produce IR"
  [pamela-model-text]
  (let [pamela-model-json (and pamela-model-text (json/read-str pamela-model-text))
        pamela-model-ir (unencode-ir-strings pamela-model-json)]
    pamela-model-ir))

(defn read-ir-file [pathstring]
  (let [pamela-model-text (slurp pathstring)]
    (read-ir-from-json-string pamela-model-text)))

;;; ------------------------------------------------------------------------
;;; ir code walking
;;; ------------------------------------------------------------------------

(def ^:dynamic *callers-of-nyi* (atom nil))

(defn nyi [& args]
  (if-not (some #(= args %) (deref *callers-of-nyi*))
    (swap! *callers-of-nyi* conj args))
  nil)

(defn walk-ir [ir fn]
  (let [listofkeys (keys ir)
        bodies (map #(get ir %) (keys ir))]
    ;;(println "keys=" listofkeys)
    ;;(println "bodies=" bodies)
    (remove nil? (map #(fn %2 (get %2 :type) %1) listofkeys bodies))))

(defn mode-ref?
  [pmr]
  ;; (println "In mode-ref? pmr=" pmr " = " (and (map? pmr)
  ;;     (= (get pmr :type) :mode-ref)))
  (and (map? pmr)
       (= (get pmr :type) :mode-ref)))

(defn deref-moderef
  [pmr]
  ;; (println "in deref-moderef pmr =" pmr " = " (get pmr :mode))
  (get pmr :mode))

(defn maybe-deref-moderef
  [form]
  (if (mode-ref? form) (deref-moderef form) form))

;;; +++ very nasty hack for selecting initial mode +++ FIND A BETTER WAY
(defn initial-mode-of [modes]
  (first (remove nil? (map (fn [[mode val]]
                             (if (= (maybe-deref-moderef val) :initial) mode nil))
                           modes))))

(defn walk-get-modes [ir type name]
  (if (and
       (= type :pclass)
       (get ir :modes))
    (let [modes (get ir :modes)
          values (map #(if (and (map? (second %))
                                (= (count (get (second %) :args)) 1)
                                (or (= (get (second %) :type) :or)
                                    (= (get (second %) :type) :and)))
                         [(first %) (maybe-deref-moderef (first (get (second %) :args)))]
                         %)
                      modes)
          initial (initial-mode-of values)]
      ;; (println "In walk-get-modes modes=" modes " values=" values " initial=" initial)
      (if initial
        { :pclass name :values values :initial initial }
        { :pclass name :values values }))))

(defn get-modes-from-ir [ir]
  (walk-ir ir walk-get-modes))

(defn walk-get-args [ir type name]
  (if (and
       (= type :pclass)
       (get ir :args))
    (let [args (get ir :args)]
      { :pclass name :args args })))

(defn get-args-from-ir [ir]
  (walk-ir ir walk-get-args))

;;; (get-modes-from-ir *testir*)
(defn compile-reference
  "Compile expression into evaluable form, used in conditions."
  [ref]
  ;; (println "in compile-reference, ref=" ref)
  (let [{type :type, names :names, pclass :pclass, args :args, mode :mode, mode-ref :mode-ref plant-id :plant-id} ref ]
    (case type
      :literal (:value ref)
      :field-ref (into [] (cons :field names))
      :method-arg-ref (into [] (if (> (count names) 1) (cons :arg-field names) (cons :arg names)))
      :pclass-arg-ref (into [] (cons :class-arg names))
      :pclass-ctor (into [] (cons :make-instance (cons pclass (cons plant-id args))))
      :mode-ref  (into [] [:mode-of (compile-reference mode-ref) mode])
      :symbol-ref names
      ref)))

(defn filter-mode [cond]
  ;;(println "in filter-mode, cond=" cond)
  (if (and (= (:type cond) :mode-reference)
           (= (:pclass cond) 'this))
    (:mode cond)
    (if (= (:type cond) :literal)
      (:value cond)
      (case (:type cond)
        (:equal :notequal :same :notsame :gt :ge :lt :le :and :or :not :implies)
        cond
        'true))))

(defn compile-proposition
  [prop]
  (let [{type :type, look-where :look-where, prop-name :prop-name args :args} prop]
    [:lookup-in look-where (into [prop-name] (map compile-reference args))]))

(defn compile-condition
  "Compile a condition into evaluable form;"
  [cond]
  ;; (println "in compile-condition, cond=" cond)
  (let [{type :type, pclass :pclass, args :args, mode :mode, value :value} cond
        numargs (count args)]
    (case type
      :mode-ref       (compile-reference cond)
      :literal        value

      (:equal :notequal :gt :ge :lt :le :same :notsame)
                      (if (= numargs 2) [type
                                         (compile-reference (first args))
                                         (compile-reference (second args))]
                          ;; surely a constructor is called for here like with the others+++
                          cond)         ; +++ unfinished - how to compile inequalities with args != 2
      :and            (if (= numargs 1)
                        (compile-condition (first args))
                        (dxp/make-AND (map (fn [part] (compile-condition part)) args)))
      :or             (if (= numargs 1)
                        (compile-condition (first args))
                        (dxp/make-OR (map (fn [part] (compile-condition part)) args)))
      :implies        (if (= numargs 2) (dxp/make-IMPLIES (compile-condition (first args))
                                                          (compile-condition (second args)))
                          cond) ; +++ unfinished - what do we want to do with a malformed implies
      :xor            (if (= numargs 2) (dxp/make-XOR (compile-condition (first args))
                                                      (compile-condition (second args)))
                          cond) ; +++ unfinished - what do we want to do with a malformed xor
      :not            (if (= numargs 1)
                        (dxp/make-NOT (compile-condition (first args)))
                        cond) ; +++ unfinished - what do we want to do with a malformed xor
      :function-call  (dxp/make-CALL (get (first args) :names)
                                     (map (fn [arg] (compile-reference arg)) (rest args)))
      :lookup-propositions (let [{where :where
                                  props :propositions} cond]
                             (dxp/make-PROPOSITIONS (compile-condition where)
                                                    (into []
                                                          (map (fn [aprop] (compile-proposition aprop))
                                                               props))))

      'true)))

(defn lvar? [lv]
  (and (map? lv)
       (= (:type lv) :lvar)))

(defn filter-probability [prob]
  (if (number? prob)
    (list prob)
    (if (lvar? prob)
      (let [name (:name prob)
            default (:default prob)]
        (list default name))
      :unknown)))

(defn consume-transitions [tr]
  ;; (println "; transition is " tr)
  (let [name (first tr)
        kws (second tr)
        trkeys (keys kws)
        trvals (map #(get kws %) trkeys)
        kwlist (apply concat (map list trkeys trvals))
        {:keys [pre post probability]} kwlist
        from-mode (compile-condition pre)
        to-mode (compile-condition post)]
    ;; (println "; transition " name "from = " pre " => " post " with probability: " probability)
    (list name from-mode to-mode (filter-probability probability))))

(defn walk-get-transitions [ir type name]
  (if (and
       (= type :pclass)
       (get ir :transitions))
    (do
      ;; (println "; transitions are " (into () (:transitions ir)))
      (let [transitions (get ir :transitions)
            canonical (map consume-transitions (into () transitions))]
        { :pclass name :transitions canonical}))))

(defn get-transitions-from-ir [ir]
  (walk-ir ir walk-get-transitions))

;;; (get-transitions-from-ir *testir*)
(defrecord MethodSignature [mname prec postc prob arglist])

(defn consume-methods [md]
  ;; (println "; method is " md)
  (let [name (first md)
        kws (first (second md))
        mdkeys (keys kws)
        mdvals (map #(get kws %) mdkeys)
        kwlist (apply concat (map list mdkeys mdvals))
        ;; (println "kwlist=" kwlist "mdkeys=" mdkeys "mdvals=" mdvals)
        {:keys [args pre post cost reward controllable primitive temporal-constraints betweens probability body]} kwlist
;;;        from-mode (filter-mode pre)
;;;        to-mode (filter-mode post)]
;;;    ;;(println "; method " name "from = " pre " => " post " with probability: " probability)
;;;    (list name from-mode to-mode (filter-probability probability))))
        precond (compile-condition pre)
        postcond (compile-condition post)]
    ;; (println "; method " name "from = " pre " => " post " with probability: " probability "args=" args)
    (MethodSignature. name precond postcond (filter-probability probability) args)))

(defn walk-get-methods [ir type name]
  ;; (println "type=" type "name=" name)
  (let [methods (get ir :methods)
        list-of-methods (into () methods)]
    (if (and (= type :pclass) methods)
      (let [canonical (map consume-methods list-of-methods)]
        ;; (println "; methods are " list-of-methods)
        {:pclass name :methods canonical}))))

(defn get-methods-from-ir [ir]
  (walk-ir ir walk-get-methods))

;;; (get-methods-from-ir *testir*)

;;; +++ need to translate class arg references
(defn consume-fields [md]
  ;; (println "; field is " md)
  (let [name (first md)
        kws (second md)
        ;;fdkeys (keys kws)
        ;;fdvals (map #(get kws %) fdkeys)
        ;;kwlist (apply concat (map list fdkeys fdvals))
        ;; - (println "kws =" kws)
        keys (into {}
                   (map (fn [[kw val]]
                               (if (= kw :initial)
                                 {kw (compile-reference val)}
                                 {kw val}))
                        kws))]
    ;;(println "; field " name "from = " pre " => " post " with probability: " probability)
    ;;(println "; field " name "keys = " keys)
    (list name keys)))

(defn walk-get-fields [ir type name]
  ;; (println [ir type name])
  (if (and
       (= type :pclass)
       (get ir :fields))
    (do
      ;; (println "; fields are " (into () (get ir "fields")))
      (let [fields (get ir :fields)
            canonical (map consume-fields (into () fields))]
        {:pclass name :fields canonical}))))

(defn get-fields-from-ir [ir]
  (walk-ir ir walk-get-fields))

(defn walk-get-pclasses [ir type name]
  (if (= type :pclass)
    (list name ir)))

(defn consume-lvar-fields [md]
  (let [fname (first md)
        kws (second md)
        init (get kws :initial)]
    (if (and init (= (get init :type) :lvar))
      (do
        ;; (println "fname=" fname "kws=" kws "init=" init)
        [fname (get init :name)])
      nil)))

(defn get-lvar-map-from-fields-of-class [ir type name]
  (if (and
       (= type :pclass)
       (get ir :fields))
    (do
      (let [fields (get ir :fields)
            lvarbindings (into [] (remove nil? (map consume-lvar-fields fields)))]
        (if (not (empty? lvarbindings))
          {:pclass name :lvars (into {} lvarbindings)})))))

(defn get-lvar-maps-from-ir [ir]
  (walk-ir ir get-lvar-map-from-fields-of-class))

(defn consume-constructor-fields
  [md]
  (let [fname (first md)
        kws (second md)
        init (get kws :initial)]
    (if (and init (= (get init :type) "pclass-ctor"))
      (let [cargs (get init :args)
            cargnames (seq (remove nil? (map (fn [arg]
                                               (if (= (get arg :type) :field-ref)
                                                 (first (get arg :names))))
                                             cargs)))]
        ;; (println "fname=" fname "kws=" kws "init=" init "args=" cargnames)
        [fname {:constructor (get init :pclass)
                :args cargnames}])
      nil)))

(defn consume-constructor-component-type-map
  [md]
  (let [fname (first md)
        kws (second md)
        init (get kws :initial)]
    (if (and init (= (get init :type) :pclass-ctor))
      (let [cargs (get init :args)
            cargnames (seq (remove nil? (map (fn [arg]
                                               (if (= (get arg :type) :field-ref)
                                                 (first (get arg :names))))
                                             cargs)))]
        ;; (println "fname=" fname "kws=" kws "init=" init "args=" cargnames)
        [fname (get init :pclass)])
      nil)))

(defn get-component-type-map
  [ir type name]
  (if (and
       (= type :pclass)
       (get ir :fields))
    (do
      (let [fields (get ir :fields)
            types  (remove nil? (map consume-constructor-component-type-map
                                     (into () fields)))]
        (if (not (empty? types))
          [name (into {} types)])))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defn get-component-type-map-from-ir
  "Returns a map of classes by class name with a map of the fields and their types."
  [ir]
  (into {} (remove nil? (walk-ir ir get-component-type-map))))

(defn get-constructors-from-fields-of-class
  [ir type name]
  (if (and
       (= type :pclass)
       (get ir :fields))
    (do
      ;;(println "; fields are " (into () (get ir "fields")))
      (let [fields (get ir :fields)
            constructors (remove nil? (map consume-constructor-fields (into () fields)))]
        (if (not (empty? constructors))
          {:pclass name :constructors constructors})))))

(defn get-constructors-from-ir [ir]
  (walk-ir ir get-constructors-from-fields-of-class))

(defn get-lvmap [pcls lvars]
  (into {}
        (remove nil? (map (fn [amap] (if (= pcls (:pclass amap)) (:lvars amap))) lvars))))

(defn get-wired-constructors [ir]
  (let [lvars (get-lvar-maps-from-ir ir)
        const (get-constructors-from-ir ir)]
    (remove nil?
            (apply concat
                   (map (fn [constr]
                          (let [pcls (:pclass constr)
                                locons (:constructors constr)
                                vars (get-lvmap pcls lvars)]
                            (if (not (empty? vars))
                              (do
                                ;;(println "pcls=" pcls "constr=" constr "locons=" locons)
                                (map (fn [[name details]]
                                       (let [cargs (:args details)
                                             cname (:constructor details)
                                             lvargs (set (remove nil?
                                                            (map (fn [anarg]
                                                                   (if (get vars anarg) anarg))
                                                                 cargs)))]
                                         ;;(println "name=" name "details=" details "cname=" cname "args=" cargs "vars=" vars "lvargs=" lvargs)

                                         (if (not (empty? lvargs)) [pcls name lvargs])))
                                     locons)))))
                        const)))))

(defn component-connectivity-map-dotted [wired-constr]
  (into {}
        (seq (map (fn [[pcls comp connections]]
                    [(with-out-str (printf "%s.%s" pcls comp))
                     (remove nil? (map (fn [[opcls ocomp ocx]]
                                         (if (and (not (= comp ocomp))
                                                  (not (empty? (set/intersection connections ocx))))
                                           (with-out-str (printf "%s.%s" opcls ocomp))))
                                       wired-constr))])
                  wired-constr))))

(defn component-connectivity-map [wired-constr]
  (into {}
        (seq (map (fn [[pcls comp connections]]
                    [comp
                     (remove nil? (map (fn [[opcls ocomp ocx]]
                                         (if (and (not (= comp ocomp))
                                                  (not (empty? (set/intersection connections ocx))))
                                           ocomp))
                                       wired-constr))])
                  wired-constr))))

(defn get-pclasses-from-ir [ir]
  (walk-ir ir walk-get-pclasses))

(defn walk-get-pclass-names [ir type name]
  (if (= type :pclass)
    [name  (into [] (get ir :inherit))]))

(defn get-pclass-names-from-ir [ir]
  (into {} (walk-ir ir walk-get-pclass-names)))

(defn walk-get-pclass-args [ir type name]
  (if (= type :pclass)
    [name  (into [] (get ir :args))]))

(defn get-pclass-args-from-ir [ir]
  (into {} (walk-ir ir walk-get-pclass-args)))

(defn tc-inherits [sli tmap]
  (if (not (empty? sli))
    (let [inherits (apply concat sli (map (fn [super] (tc-inherits (get tmap super) tmap)) sli))]
      (set inherits))))

(defn get-pclass-types-from-ir [ir]
  (let [all-inherited (get-pclass-names-from-ir ir)]
    (into {}
          (map (fn [[name sl-inherits]]
                 [name (tc-inherits sl-inherits all-inherited)])
               all-inherited))))

(defn is-a [obj typename alltypes]
  (let [type-of-obj (conj (get alltypes obj) obj)]
    (if type-of-obj
      (if (not (empty? (set/intersection (set [typename]) type-of-obj)))
        true
        false))))

(defn type-of [comp comptypemap]
  (let [type (remove nil? (map (fn [tm]
                                 (get tm comp))
                               comptypemap))]
    (if (not (empty? type))
      (first type)
      nil)))

;(defn type-of [comp comptypemap]
 ; (get comptypemap comp))

(defn components-of-type
  "Returns a list of components that match searchtype in all classes.
   componenttypemap is the result of a call to (irx/get-component-type-map-from-ir model)
   alltypes is the result of a call to (irx/get-pclass-types-from-ir model)
   conmap is the result of a call to (irx/component-connectivity-map (irx/get-wired-constructors model))"
  [componenttypemap alltypes conmap searchtype]
  (apply concat
         (remove empty?
                 (map (fn [[pclass components]]
                        (remove empty?
                                (map (fn [[compname comptype]]
                                       ;; If the component is of type searchtype, we have found one
                                       (if (is-a comptype searchtype alltypes)
                                         [pclass compname (get conmap compname)]))
                                     components)))
                      componenttypemap))))

(defn walk-get-lvars [ir type lvs]
  (if (and
       (= type :lvars)
       (get ir :lvars))
    (let [lvars (get ir :lvars)]
      (map (fn [[ name val ]] name) lvars))))

(defn get-lvars-from-ir [ir]
  (apply concat (walk-ir ir walk-get-lvars)))

;;; (get-fields-from-ir *testir*)

(defn testall [ir]
  (println "pclasses")
  (pprint (get-pclass-names-from-ir ir))
  (println "args")
  (pprint (get-args-from-ir ir))
  (println "modes:")
  (pprint (get-modes-from-ir ir))
  (println "fields:")
  (pprint (get-fields-from-ir ir))
  (println "transitions:")
  (pprint (get-transitions-from-ir ir))
  (println "methods:")
  (pprint (get-methods-from-ir ir)))

;;; (testall *testir*)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; spamela

(defn get-modes
  [pcname modes]
  ;;(println "in get-modes")
  (let [themodes (remove nil? (map (fn [amode]
                                     (if (= (get amode :pclass) (first pcname))
                                       { :modes (get amode :values) }))
                                   modes))]
    ;;(println [:get-modes pcname modes themodes])
    themodes))

(defn get-args
  [pcname args]
  ;;(println "in get-args")
  (let [theargs (remove nil? (map (fn [aargs]
                                     (if (= (get aargs :pclass) (first pcname))
                                       { :args (get aargs :args) }))
                                   args))]
    ;; (println [:get-args pcname args theargs])
    theargs))

(defn get-fields
  [pcname fields]
  ;;(println "in get-fields")
  (let [thefields (remove nil? (map (fn [afield]
                                     (if (= (get afield :pclass) (first pcname))
                                       { :fields (get afield :fields) }))
                                   fields))]
    ;;(println [:get-fields pcname fields thefields])
    thefields))

(defn get-transitions
  [pcname transitions]
  ;;(println "in get-transitions")
  (let [thetransitions (remove nil? (map (fn [atransition]
                                           (if (= (get atransition :pclass) (first pcname))
                                             { :transitions (get atransition :transitions) }))
                                         transitions))]
    ;;(println [:get-transitions pcname transitions thetransitions])
    thetransitions))

(defn get-methods
  [pcname methods]
  ;; (println "in get-methods pcname=" pcname " methods=" methods)
  (let [themethods (remove nil? (map (fn [amethod]
                                     (if (= (get amethod :pclass) (first pcname))
                                       { :methods (get amethod :methods) }))
                                   methods))]
    ;;(println [:get-methods pcname methods themethods])
    themethods))

(defn get-spamela-class-from-ir
  [jir name]
  ;; (println "in get-spamela-class-from-ir name= " name)
  (let [args (get-args-from-ir jir)
        modes (get-modes-from-ir jir)
        fields (get-fields-from-ir jir)
        transitions (get-transitions-from-ir jir)
        methods (get-methods-from-ir jir)]
    (let [inherits (if (not (empty? (second name))) [[:inherits (second name)]] #_[[:inherits []]])
          args (get-args name args)
          modes (get-modes name modes)
          fields (get-fields name fields)
          transitions (get-transitions name transitions)
          methods (get-methods name methods)
          spamela-class (concat inherits args modes fields transitions methods)]
      (into {} spamela-class))))

(defn json-ir-to-spamela
  [jir verbose]
  (let [classnames (get-pclass-names-from-ir jir)]
    (map (fn [name]
           { (first name) (get-spamela-class-from-ir jir name)})
         classnames)))

(defn generate-spamela
  [args]
  (let [model-from-json (args :pm-json)
        verbosity (args :verbose)]
    (def ^:dynamic *testir* model-from-json)
    (json-ir-to-spamela model-from-json verbosity)))

(defn output-spamela-to-a-file
  [destination spam]
  (with-open [ostrm (java.io.OutputStreamWriter.(java.io.FileOutputStream. destination) "UTF-8")]
    ;;(xml/emit reqs ostrm)
    (.write ostrm (with-out-str (pprint spam)))
    (.write ostrm "\n")))

(defn make-spamela
  "generate spamela."
  [args]
  (let []
    (binding [
              pamela-model (args :model)
              outfile (args :outfile)
              verbosity (args :verbose)
              ]
      (if (> verbosity 0) (printf "generating spamela for: %s%n" "(titleof model)"))
      (let [pamela-model-text (and pamela-model
                                   (.exists (io/file pamela-model))
                                   (slurp pamela-model))
            ;; - (println "pamela-model-text =")
            ;; - (pprint pamela-model-text)
            pamela-model-json (and pamela-model-text (json/read-str pamela-model-text))
            pamela-model-json (unencode-ir-strings pamela-model-json)
            ;; - (println "pamela-model-json =")
            ;; - (pprint pamela-model-json)
            spamela (if pamela-model-json
                      (generate-spamela
                       (merge args { :pm-json pamela-model-json}))
                      (println "file not found: " pamela-model))
            - (output-spamela-to-a-file outfile spamela)]
        (if (and (> verbosity 0) spamela)
          (do (printf "spamela output to %s%n" outfile) (pprint spamela)))
        nil))))

(def dcryppstest-model "/Users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile_guidance_v5.ir.json")
(def missile-guidance-model dcryppstest-model)
(def missile-guidance-dp "/Users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile_guidance_v5.dp.json")
;(def dcryppstest-model "/users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile-guidance.json")
;(def dcryppstest-model "/users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile-guidance-compatible.json")

;;; Original handmade pamela

;(def desiredproperties "/Users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile-guidance.dp.json")
;(def desiredproperties "/Users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/missile-guidance-compatible.dp.json")
(def simple-model "/users/paulr/checkouts/bitbucket/CASE-Vanderbilt-DOLL/data/missile-guidance/simplesample.json")
;;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; ****** DAN, Change these two to point at where the missile guidance json
;;;        file and the DP json file respectively can be found in your hierarchy.
;;; for Dan uncomment these after replacing the ellipses with something sensible:
;;; DAN, you will need to update the following to point to the files in
;;;      question in your directory hierarchy.  Not that the
;;;      second one -- the attack-model should be the file generated by the
;;;      DMCP phase. Uncomment them after you have fixed the pathnames!

;;; (def dcryppstest-model ".../data/missile-guidance/missile_guidance_v5.ir.json")
;;; (def attack-model ".../data/missile-guidance/attack-plan.json")
;;; (def desiredproperties ".../data/missile-guidance/MissileGuidanceUnit.Impl-20190809.dp.json")

;;;(def debugging-model "/users/paulr/checkouts/doll/projects/pamela/pmcgp/data/missile-guidance.json")
;;;(def plannertest-model "/users/paulr/checkouts/doll/projects/pamela/pmcgp/data/plannertest.json")

(defn -main
  []
  (let [args {
              :model dcryppstest-model
              :verbose 1
              :outfile "spamela.file" }]
    (make-spamela args)))

;;; (-main)

;;; example calls
;; (def pamela-model *testir*)

;;(get-pclass-types-from-ir pamela-model)
;;(get-pclass-names-from-ir pamela-model)
;;(get-pclasses-from-ir pamela-model)
;;(get-lvar-maps-from-ir pamela-model)
;;(get-constructors-from-ir pamela-model)
;;(get-wired-constructors pamela-model)
;;(get-component-type-map-from-ir pamela-model)
;;(component-connectivity-map (get-wired-constructors pamela-model))
;;(type-of 'ins (get-component-type-map-from-ir pamela-model)) ;yes
;;(is-a 'INS 'Sensor (get-pclass-types-from-ir pamela-model)) ;yes
;;(is-a (type-of 'ins (get-component-type-map-from-ir pamela-model)) 'Sensor (get-pclass-types-from-ir) (type-of 'ins (get-component-type-map-from-ir pamela-model)) ; yes
;;(is-a 'ins 'INS (get-pclass-types-from-ir pamela-model)) ;no
;;(is-a (type-of 'ins (get-component-type-map-from-ir pamela-model)) 'Sensor (get-pclass-types-from-ir pamela-model)) ; yes

;;; (keys *testir*)


;;; Fin
