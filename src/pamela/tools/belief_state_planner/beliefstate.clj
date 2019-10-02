;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.beliefstate
  "Belief State Planning"
  (:require [clojure.string :as string]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.tools.logging :as log]
            [environ.core :refer [env]]
            ; [avenir.utils :as au :refer [as-boolean]]
            ; [beliefstate.observe :as observe]
            )
  (:gen-class))

;(in-ns 'pamela.tools.belief-state-planner.beliefstate)

(def ^:dynamic *print-warnings* true)

;;;    "Defines the basic belief state class that represents the domains
;;;     proposition-types propositions and variables of the belief state."
(defrecord BeliefState
  [domains variables proposition-types propositions])

(def ^:dynamic *current-belief-state* (BeliefState. (atom nil) (atom nil) (atom nil) (atom nil)))

(def ^:dynamic *initialized-mft* nil)

;;; A simple macro to produce code that uses a provided belief state
;;; if the provided belief state is nil the current belief state is
;;; used instead.

(defn bs-complete-reset
  []
  (def ^:dynamic *current-belief-state* (BeliefState. (atom nil) (atom nil) (atom nil) (atom nil))))

(defmacro with-belief-state [bs & body]
  "This macro provides a simple way of switching between belief states."
  `(binding [*current-belief-state* (or ~bs *current-belief-state*)]
      ~@body))

(defmacro c-domains [] `(.domains *current-belief-state*))
(defmacro c-variables [] `(.variables *current-belief-state*))
(defmacro c-proposition-types [] `(.proposition-types *current-belief-state*))
(defmacro c-propositions [] `(.propositions *current-belief-state*))


(defn current-belief-state
  "Packages up the belief state into a list representation"
  [& [bs]]
  (with-belief-state bs
    (list (c-domains) (c-variables) (c-proposition-types) (c-propositions))))

(defn set-belief-state [four-tuple & [bs]]
 "Unpacks a list representation of a belief state."
 (with-belief-state bs
   (let [[d v pt p] four-tuple]
     (reset! (c-domains) d)
     (reset! (c-variables) v)
     (reset! (c-proposition-types) pt)
     (reset! (c-propositions) p))))

(defn find-prop [pname & [bs]]
  (with-belief-state bs
    (first (filter #(= pname (:ptype %)) @(c-propositions))))) ;+++ptype

(defn find-variable
  "Finds a variable instance with the name (vname)"
  [vname & [bs]]
  (with-belief-state bs
    (let [var (get @(c-variables) vname)]
      ;;(when (null var) (warn "Variable ~a not found." vname))
      var)))

(defn mult-distribution [gain var-update] var-update) ;+++ need a real definition for this
(defn add-distribution [new-belief-var var-val] var-val) ;+++ need a real definition for this
(defn normalize-distribution [fused-belief-var] fused-belief-var)  ;+++ need a real definition for this

(defn add-belief-variable
  "Adds new evidence to a belief about a variable."
  [varname val gain & [bs]]
  (with-belief-state bs
    (let [var (find-variable varname)
          var-val (and var (:value var))
          var-update {val 1.0}
          new-belief-var (mult-distribution gain var-update) ; gain
          fused-belief-var (add-distribution new-belief-var var-val) ; fuse
          updated-belief-var (normalize-distribution fused-belief-var)] ; renormalize
      (reset! (:value var) updated-belief-var))))

;; (defun belief-state-equal (b1 sbs &optional bs)
;;   "Compares a symbolic belief state to a given (or current) belief state.
;;    This is primariliy to support the writing of regression tests."
;;   (with-belief-state bs
;;     (let ((used-variables nil)
;;           (cbs (current-belief-state)))
;;       (unwind-protect
;;         (progn
;;           (set-belief-state b1)
;;           (destructuring-bind (props vars) sbs
;;             ;;(trdbg (:dad 12) "props=~a vars=~a" props vars)
;;             ;; Verify the propositions
;;             (dolist (p props)
;;               (destructuring-bind (subj prop obj) p ; +++ assumes binary propositions
;;                 (let ((matchprop (find-prop prop)))
;;                   (if (null matchprop) (return-from belief-state-equal nil))
;;                   (pushnew (subject matchprop) used-variables)
;;                   (pushnew (object matchprop) used-variables))))
;;             (flet ((variable-value (vname)
;;                      (dolist (uv used-variables :not-found)
;;                        (if (eql (vname uv) vname)
;;                            (return-from variable-value (vvalue uv))))))
;;                ;; Verify the variables
;;                (dolist (avar used-variables)
;;                  (let* ((var (find-variable avar))
;;                         (mvar (cdr (assoc avar vars))))
;;                    (if (null var) (return-from belief-state-equal nil))
;;                      (unless (belief-equal (vvalue var) mvar)
;;                        (return-from belief-state-equal nil)))))
;;             t))
;;         (set-belief-state cbs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Belief-state representation and protocol

;;; domains

(defn make-domain
  "A domain specifies the range of values that a belief can have.
     For example a variable called :COLOR might have a domain of (:RED
     :ORANGE :YELLOW :GREEN :BLUE :INDIGO :VIOLET)."
  [dname vals]
  { :name dname, :values (atom vals), :type :domain })

(defn dname [adomain] (get adomain :name))
(defn dvalues [adomain] (get adomain :values))

(defmulti print-object (fn [obj stream] (:type obj)))

(defmethod print-object
  :domain [object stream]
  (.write stream (format "#<Domain %s with values %s>" (dname object) @(dvalues object))))

(defn get-domain
  "Finds a named domain in the belief state."
  [name & [bs]]
  (with-belief-state bs
    (get @(c-domains) name)))

(defn get-domain-values
  "Returns the list of values for a named domain."
  [name & [bs]]
  (with-belief-state bs
    (let [domain (get-domain name)]
      (when domain
        @(dvalues domain)))))

(defn add-domain
  "Add a new domain to the belief state."
  [nname values & [bs]]
  (with-belief-state bs
    (let [new-domain (make-domain nname values)]
      (reset! (.domains *current-belief-state*)
              (merge @(.domains *current-belief-state*) { nname new-domain })))))

(defmacro def-domain
  "Macro for defining a new domain in the belief state."
  ;; +++ check format of name and values +++
  [name & values]
  `(do (add-domain '~name '~values) '~name))

(def-domain orphan)

;;; (def-domain foo :A :B :C)
;;; (def-domain bar :D :E :F)
;;; (get-domain 'foo)
;;; (get-domain-values 'foo)
;;; (get-domain 'bar)
;;; (get-domain-values 'bar)

(defmulti describex (fn [obj & [stream]] (:type obj)))

;  Print out a domain in a human readable form
(defmethod describex :domain [object & [stream]]
  (let [output (format "Domain %s%n" (dname object))]
    (if stream (.write stream output) (print output))
    (when @(dvalues object)
      (if stream (.write stream (format "   Values: %n")) (print (format "   Values: %n")))
      (doseq [v @(dvalues object)]
        (if stream (.write stream (format "      %s%n" v))
            (print (format "      %s%n" v))))
      (if stream (.write stream (format "%n"))
            (print (format "%n"))))))

;;; (describex (get-domain 'foo))
;;; (describex (get-domain 'bar))

(defmacro describe-domain
  "Describe a domain given its symbolic name."
  [dname]
  `(if (get-domain '~dname)
     (describex (get-domain '~dname))
    :no-such-domain))

;;; (describe-domain foo)
;;; (describe-domain bar)

(defmacro undef-domain
  "A macro for undefining a domain."
  [dname]
  `(let [existing-domain# (get-domain '~dname)]
     (if existing-domain#
       (do
         (reset! (c-domains) (dissoc @(c-domains) '~dname))
         '(~dname removed))
       '(~dname not found))))

;;; (undef-domain foo)

(defn print-domains
  "A debugging function that prints out all of the domains."
  [& [stream]]
  (cond (nil? @(c-domains)) (.write (or stream *out*) (format "%nNo domains defined.%n%n"))
        :else (do
                (.write (or stream *out*) (format "%nDomains:%n"))
                (doseq [dm (seq @(c-domains))]
                  (.write (or stream *out*) (format "   %s values=%s%n" (first dm) @(:values (second dm)))))
                (.write (or stream *out*) (format "%n"))))
  nil)

;;; (print-domains)

;;; Belief-state

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Variables
;;; A variable can take a distribution of values
;;; A variable takes values of a given domain
;;; Each value is in the distribution comes with:
;;; 1. a probability
;;; 2. a set of supports.

(defn make-bs-variable
  "A variable is the basic unit of a belief and about which observations
     directly provide evidence for.Variables:
     A variable can take a distribution of values
     A variable takes values of a given domain
     Each value is in the distribution comes with:
     1. a probability
     2. a set of supports."
  [vname vtype vval]
  { :name vname, :vtype vtype, :value (atom vval), :type :bs-variable})

(defn vname [avar] (get avar :name))
(defn vtype [avar] (get avar :vtype))
(defn vvalue [avar] (get avar :value))

(defn total-distribution [map-dist]
  (reduce + (vals map-dist)))

;;; If the variable describes a type with enumerated values set the belief
;;; to a flat distribution over those possibilities.
;;; Don't change if not an enumerated type variable.

(defn get-variable
  "Get the named variable or nil if it doesn't exist"
  [vname & [bs]]
  (with-belief-state bs
    (get @(c-variables) vname)))

(defn make-flat-distribution
  "Sets a variable to a flat distribution over its domain. In other words
   no particular belief in any value."
  [object & [bs]]
  (with-belief-state bs
    (if (or (keyword object) (symbol? object))
      (let [variable (get-variable object)]
        (when variable (make-flat-distribution variable)))
      (if (and (map? object) (= (:type object) :bs-variable))
        ;; Sets a variable to a flat distribution over its domain. In other words
        ;; no particular belief in any value.
        (let* [values (get-domain-values (vtype object))
               dsize (count values)]
              (when values
                (let [fprob (/ 1.0 dsize)]
                  (reset! (vvalue object) (map #({% fprob}) values)))))))))

(defn set-true-variable-value
  "Sets the value of a variable to a specific value."
  [object newvalue & [bs]]
  (with-belief-state bs
    (if (or (keyword object) (symbol? object))
      (let [variable (get-variable object)]
        (if variable (set-true-variable-value variable newvalue)))
      (let [domain-values (get-domain-values (vtype object))
            nvals (count domain-values)]
        (if (and (> nvals 0) (contains? domain-values newvalue))
          (reset! (vvalue object)
                  (map #(if (= newvalue %) {% 1.0} {% 0.0}) domain-values))
          (if *print-warnings*
            (printf "Warning: Attempt to set value of variable ~a to an illegal value (~a)."
                    (vname object) newvalue)))))))

(defn make-normalized-distribution
  "Make belief distribution add to 1"
  [object & [bs]]
  (with-belief-state bs
    (if (or (keyword object) (symbol? object))
      (let [variable (get-variable object)]
        (if variable (make-normalized-distribution variable)))
      (let [distn @(vvalue object)]
        (if (map? distn)
          (let [totprob (total-distribution distn)
                flat (/ 1.0 (count distn))
                adj (if-not (= totprob 0.0) (/ 1.0 totprob) 0.0)]
            (reset! (vvalue object)
                    (map #(if (= adj 0.0) {(first %) flat} {(first %) (* (second %) adj)}) (seq distn)))))))))

;;+++ do me
;; (defmethod print-object ((object bs-variable) stream)
;;   "Prints a variable"
;;     ;; +++ do we want to print the value distribution?
;;     (format stream "#<Variable ~a with type ~a>" (vname object) (vtype object)))

(defn describe-bs-variable
  "Prints a variable in a human readable form."
  [object & [stream]]
  (let [strm (or stream *out*)]
    (.write strm (format "Variable %s %n   Type %s %n" (get object :name) (get object :vtype)))
    (when @(vvalue object)
      (let [vals @(vvalue object)]
        (cond
          (> (count vals) 1)
          (do (.write strm (format "   Value: %n"))
              (doseq [v @(vvalue object)]
                (.write strm (format "      %s (with probability %s)%n" (first v) (second v)))))

          (= (count vals) 1)
          (do (.write strm (format "   Value: "))
              (doseq [v @(vvalue object)]
                (.write strm (format "      %s %n" (first v)))))
          :else nil)))))


;; (defmethod describe-variable ((object symbol) &optional (stream *standard-output*))
;;   "Prints a variable in a human readable form."
;;   (let ((var (get-variable object)))
;;     (cond (var (describe-variable var stream))
;;           (:otherwise (format stream "No variable defined with name: ~a.~%" object)))))

(defn add-variable
  "Add a new variable to the belief state"
  [vname vtype values & [bs]]
  (with-belief-state bs
    ;; +++ check format +++
    ;; +++ do something with values +++
    ;; If necessary make a new domain with no values (can be defined later).
    (let [existing-domain (get @(c-domains) vtype)]
      (if-not (or existing-domain (not vtype) (not values)) (add-domain vtype values))
      (let [existing-variable (get @(c-variables) vname)
            new-variable (make-bs-variable vname vtype nil)]
          (reset! (c-variables) (merge @(c-variables) {vname new-variable}))))))

(defmacro def-variable
  "Macro for defining new variables"
  [name type & values]
  `(do
     (add-variable '~name '~type '~values)
     '~name))

;;; (def-variable quux bar)
;;; (def-variable azerty bof :q :w :e :r :t :y)

(defmacro undef-variable
  "Macro for removing variables from the belief state."
  [vname]
  `(let [existing-variable# (get @(c-variables) '~vname)]
     (if existing-variable#
       (do
         ;(printf "%s%n" existing-variable#)
         (reset! (c-variables) (dissoc @(c-variables) '~vname))
         '(~vname removed))
        '(~vname not found))))

;;; (undef-variable azerty)
;;; (undef-variable azerty2)
;;; (undef-variable psw32431)

(defn print-variables
  "A debugging aid.  Prints out the state of all variables in human readable form."
  [& [stream]]
  (let [strm (or stream *out*)]
    (if (nil? @(c-variables))
      (.write strm (format "%nNo variables defined.%n%n"))
      (do
        (.write strm (format "%nVariables%n"))
        (doseq [var (seq @(c-variables))]
          (.write strm (format "   %s type=%s%n" (get (second var) :name) (get (second var) :vtype))))
        (.write strm (format "%n"))))))

;;; (print-variables)

(defn get-belief-in-variable
  "Returns the belief in a particular value of a variable."
  [vname vbel & [bs]]
  (with-belief-state bs
    (let [variable (get-variable vname)]
      (if (nil? variable)
        (do
          (if *print-warnings* (printf "Warning: Unknown variable referenced: %s%n" vname))
          0.0)
        (or (get @(get variable :value) vbel) 0.0)))))

;;; (get-belief-in-variable 'quux :E)
;;; (get-belief-in-variable 'quuxy :E)

(defn set-belief-in-variable
  "Sets the value of a variable."
  [vname vbel prob & [bs]]
  (with-belief-state bs
    (let [variable (get-variable vname)]
      (if (nil? variable)
        (if *print-warnings* (printf "Warning: Unknown variable referenced: %s%n" vname))
        ;;+++ check the vbel is in the domain of vname
        (do (reset! (get variable :value) (merge @(get variable :value) {vbel prob}))
            prob)))))

;;; (set-belief-in-variable 'quuxy :E 0.5)
;;; (set-belief-in-variable 'quux :E 0.6)


(defn get-variable-type
  "Get the type of the named variable or nil if it doesn't exist"
  [vname & [bs]]
  (with-belief-state bs
    (let [varobj (get-variable vname)]
      (if-not varobj
        (if *print-warnings* (printf "Warning: Unknown variable referenced: %s%n" vname))
        (get varobj :vtype)))))

;;; (get-variable-type 'quuxy)
;;; (get-variable-type 'quux)

(defn get-domains
  "For use with mapcan"
  [vr & [bs]]
  (with-belief-state bs
    (let [dom (get-variable-type vr)]
      ;;(if dom (list dom))
      dom)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Propositions

;; (defclass bs-proposition-type ()
;;   ((name :initarg :name :initform nil)
;;    (subjecttype :initarg :subject-type :initform nil)
;;    (objecttype :initarg :object-type :initform nil))
;;   (:documentation
;;     "A belief is a collection of a propositions over variables.
;;      A proposition type defines a class of propositions."))

(defn make-bs-proposition-type
     "A belief is a collection of a propositions over variables.
      A proposition type defines a class of propositions."
  [pname subjecttype objecttype]
  {:pname pname, :subjecttype subjecttype, :objecttype objecttype})

(defn pname [abspt] (get abspt :pname))
(defn subjecttype [abspt] (get abspt :subjecttype))
(defn objecttype [abspt] (get abspt :objecttype))

;; +++ do me
;; (defmethod print-object ((object bs-proposition-type) stream)
;;   "Prints a proposition type."
;;   (with-slots (name subjecttype objecttype) object
;;     (format stream "#<Proposition Type ~a (~a ~a)>" name (or subjecttype "*") (or objecttype "*"))))

(defn add-proposition-type
  "Adds a new proposition type to the belief state."
  [name stype otype & [bs]]
  (with-belief-state bs
    ;; If necessary make a new domain with no values (can be defined later).
    (let [existing-sdomain (get @(c-domains) stype)
          existing-odomain (get @(c-domains) otype)]
      (when (and stype (not existing-sdomain)) (add-domain stype nil))
      (when (and otype (not existing-odomain)) (add-domain otype nil)))
    (let [new-proposition (make-bs-proposition-type name stype otype)]
      (reset! (c-proposition-types) (merge @(c-proposition-types) {name new-proposition}))
      name)))

;;; (add-proposition-type 'spouse 'mary 'john)
;;; @(c-proposition-types)
;;; (print-domains)

(defmacro def-proposition-type
  "A macro for defining new proposition types."
  [name & [stype otype]]
  ;; +++ check format +++
  `(add-proposition-type '~name '~stype '~otype))

;;; (def-proposition-type spousex maryx johnx)
;;; @(c-proposition-types)
;;; (print-domains)

(defmacro undef-proposition-type
  "A macro for removing proposition types from the belief state."
  [name]
  `(let [existing-ptypes# (get @(c-proposition-types) '~name)]
     (if-not existing-ptypes#
       '(~name not found)
       (do
         (reset! (c-proposition-types) (dissoc @(c-proposition-types) '~name))
         '(~name removed)))))

;;; (undef-proposition-type aspouse)
;;; (undef-proposition-type spouse)
;;; @(c-proposition-types)

(defn print-proposition-types
  "A debugging aid. Prints out all of the propositon types in a human readable form."
  [& [stream]]
  (let [strm (or stream *out*)]
    (if (nil? @(c-proposition-types))
      (.write strm (format "%nNo proposition types defined.%n%n"))
      (do
       (.write strm (format "%nProposition types:%n"))
       (doseq [pt (seq @(c-proposition-types))]
         (.write strm (format "    %s %n" (get (second pt) :pname))))
       (.write strm (format "%n"))))))

;;; (print-proposition-types)

(defn get-proposition-type
  "Get the named proposition type or nil if it doesn't exist"
  [ptname & [bs]]
  (let [acpt (nth (current-belief-state) 2) ; @(c-proposition-types)
        cpt (if (= (type acpt) clojure.lang.Atom)
              @acpt
              (do (println "Didn't get an atom:" (type acpt)) nil))]
    (if-not (nil? cpt)
      (with-belief-state bs
        (let [vals (filter
                    #(= ptname (get (second %) :pname))
                    cpt)]
          (first vals))))))

;;; (get-proposition-type 'spousex)
;;; (get-proposition-type :is-a)

;;; Build-in proposition types

(def-proposition-type :is-a)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Adding propositions, removing propositions, finding propositions

;; (defclass proposition ()
;;   ()
;;   (:documentation
;;     "A belief is a collection of a propositions over variables."))

;; (defmethod get-proposition-types ((pr proposition)) nil)

;; (defclass binary-proposition (proposition)
;;   ((ptype :initarg :ptype :accessor ptype)
;;    (subject :initarg :subject :accessor subject)
;;    (object :initarg :object :accessor object))
;;   (:documentation
;;    "A binary proposition has two variables.
;;     eg: A binary proposition - :Fred :loves :Jane"))

(defn make-binary-proposition
   "A binary proposition has two variables.
    eg: A binary proposition - :Fred :loves :Jane"
  [ptype subject object]
  {:ptype ptype, :subject subject, :object object :type :binary})

(defn bp-ptype [obj] (get obj :ptype))
(defn bp-subject [obj] (get obj :subject))
(defn bp-object [obj] (get obj :object))

;; (defmethod get-proposition-types ((pr binary-proposition))
;;   (list (ptype pr)))

;; (defmethod print-self ((pr binary-proposition) &optional (stream *standard-output*))
;;   "Prints the binary proposition"
;;   (format stream "~a ~a ~a" (subject pr) (ptype pr) (object pr)))

(defn add-binary-proposition
  "Adds a binary proposition to the belief state."
  [ptype sobj oobj & [bs]]
  (with-belief-state bs
    (when (and sobj (not (get-variable sobj)))
      (add-variable sobj nil nil))
    (when (and oobj (not (get-variable oobj)))
      (add-variable oobj nil nil))
    (if-not (get-proposition-type ptype)
      (add-proposition-type ptype (get-variable-type sobj) (get-variable-type oobj)))
    (let [newprop (make-binary-proposition ptype sobj oobj)]
      (reset! (c-propositions) (cons newprop @(c-propositions))))))

;;; (add-binary-proposition :is-a :mary :woman)
;;; (add-binary-proposition :is-a :pig :animal)

(defn print-propositions
  "A debugging aid.  Prints out all propositions of the belief in human readable form"
  [& [stream]]
  (let [strm (or stream *out*)]
    (.write strm (format "Propositions:%n"))
    (doseq [p @(c-propositions)]
      (.write strm "   ")
      ;;+++(print-self p strm)
      ;; +++ hardwired for binary propositions -- fix
      (let [{pt :ptype, sj :subject, obj :object} p]
        (.write strm (format "(%s %s %s)" pt sj obj))
        (.write strm (format "%n"))))))

;;; (print-propositions)

;+++(defmethod get-variables ((pr proposition)) nil)

(defn get-binary-proposition-variables
  "Returns a list of all variables in a proposition."
  [pr]
  (list (bp-subject pr) (bp-object pr)))

(defn get-variables-in-propositions
  "Returns the set of all variables in all propositions."
  [& [prs]]
  (let [prsinbs (or prs @(c-propositions))
        vars (and prsinbs (apply #'concat (map #'get-binary-proposition-variables prsinbs)))] ;+++ make general to all prop types
    (set vars)))

;;; (get-variables-in-propositions)

(defn get-domains-in-variables
  "Returns a list of all domains used in all variables."
  [& [vrs]]
  (let [vars (or vrs (keys @(c-variables)))
        doms (filter #(not (nil? %)) (map #'get-domains vars))]
    (printf "get-domains-in-variables: vars=%s %s%n" vars (map #'get-domains vars))
    (set doms)))

;;; (get-domains-in-variables)

;; (defn get-used-proposition-types
;;   "Returns a list of all used proposition types."
;;   [& [prs]]
;;   (set (map #'get-proposition-types (or prs @(c-propositions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Belief state

(defn clear-belief-state [& [bs]]
  "Removes all variables and propositions of a belief state. Note that it
   does not remove the domains or proposition types because it assumes that
   this meta information will be required."
  (with-belief-state bs
    (def ^:dynamic *current-belief-state*
      (BeliefState. (c-domains) (atom nil) (c-proposition-types) (atom nil)))))
;;; *Merge question - prior line or thyis one?+++      (BeliefState. (c-domains) (c-variables) (atom nil) (atom nil)))))

(defn describe-belief-state
  "A debugging aid. This function prints out the complete belief state. in
   human readable form."
  []
  (let [vnames (get-variables-in-propositions @(c-propositions))
        variables (vec (map find-variable vnames))
        domains (get-domains-in-variables vnames)
        ; ptypes (get-used-proposition-types (c-propositions))
        ]
    (printf "%nBELIEF STATE%n%n")
    ;;(printf "vars=%s doms=%s%n" vnames domains)
    (when @(c-propositions)
      ;; Print out the domains
      (printf "DOMAINS:%n")
      (doseq [dom domains]
        ;;(println dom)
        (describex (get-domain dom))
        (printf "%n"))
      ;; Print out the variables
      (printf "%nVARIABLES:%n")
      (doseq [var variables]
        ;;`(describe-variable ~var)
        (describe-bs-variable var)
        (printf "%n"))
      ;;; Print out the proposition types (maybe not)
      ;(printf "~%PROPOSITION TYPES:~%")
      ;(dolist (pt ptypes) (describe-proposition-type var stream))
      ;; Print out the propositions
      (print-propositions)
      ;;(printf "~%PROPOSITIONS:~%")
      ;; (doseq [pr @(c-propositions)]
      ;;   (printf "   ")
      ;;   (print-self pr)) ;+++ generalize to non binary propositions
      (printf "%n"))))

(defmacro c-proposition-types [] `(.proposition-types *current-belief-state*))
(defmacro c-propositions [] `(.propositions *current-belief-state*))

(defn copy-variables
  "Make a snapshot of current variable values -- that are implemented as locations"
  [vmap]
  (into {}
         (map
          #(let [[name defn] %]
             ;;(println "name =" name "defn =" defn)
             { name (merge defn {:value (atom @(get defn :value))})}
             )
          vmap)))

(defn copy-belief-state
  "A deep copy of a belief state."
  [& [bs]]
  (with-belief-state bs
    (BeliefState. (atom @(c-domains))
                  (atom (copy-variables @(c-variables)))
                  (atom @(c-proposition-types))
                  (atom @(c-propositions)))))

;;; (describe-belief-state)

(defn get-current-belief-state-symbolic
  "Produces an s-expression form of a belief state."
   [& [bs]]
   (with-belief-state bs
     {:propositions (map #(list  (:ptype %) (:subject %) (:object %)) @(c-propositions)),
      :variables (into {} (concat
                           (filter #(not (nil? %))
                                   (map #(let [bsvar (find-variable %)]
                                           (and bsvar (list (vname bsvar) (vvalue bsvar))))
                                        (concat (map #(:subject %) @(c-propositions))
                                                (map #(:subject %) @(c-propositions)))))))}))
;;; (get-current-belief-state-symbolic)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Helpers for switching state.

(defn set-variable
  "Sets the value of a variable."
  [vname vbel & [bs]]
  (with-belief-state bs
    (let [variable (get-variable vname)]
      (if (nil? variable)
        (if *print-warnings* (printf "Warning: Unknown variable referenced: %s%n" vname))
        ;;+++ check the vbel is in the domain of vname
        (do (reset! (get variable :value) {vbel 1.0})
            vbel)))))

;;; Fin
