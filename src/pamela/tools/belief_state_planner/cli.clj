;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

(ns pamela.tools.belief-state-planner.cli
  "DOLL Monte Carlo Planner (DMCP)"
  (:require [clojure.tools.cli :as cli]
            [clojure.java.io :refer [output-stream]]
            [clojure.java.io :as io]
            [mbroker.rabbitmq :as mq]
            [langohr.core :as rmq]
            [langohr.exchange :as le]
            [langohr.queue :as lq]
            [langohr.consumers :as lc]
            [langohr.channel :as lch]
            [clojure.string :as string]
            [tpn.fromjson]
            [random-seed.core :refer :all]
            [clojure.repl :refer [pst]]
            [clojure.tools.cli :refer [parse-opts]]
            [clojure.pprint :as pp :refer [pprint]]
            [clojure.data.json :as json]
            [environ.core :refer [env]]
            [avenir.utils :as au :refer [as-boolean]]
            [pamela.unparser :as pup]
            ;;[dcrypps.common.core :as dc :refer :all]
            ;;[dcrypps.attack-model-generator.desirable-properties :as dp :refer :all]
            [pamela.tools.belief-state-planner.imagine :as imag]
            [pamela.tools.belief-state-planner.coredata :as global]
            [pamela.tools.belief-state-planner.runtimemodel :as rtm]
            [pamela.tools.belief-state-planner.montecarloplanner :as bs]
            [pamela.tools.belief-state-planner.simplify :as simp]
            [pamela.tools.belief-state-planner.buildir :as bir]
            [pamela.tools.belief-state-planner.dmcgpcore :as core]
            [pamela.tools.belief-state-planner.expressions :as dxp]
            [pamela.tools.belief-state-planner.ir-extraction :as irx]
            [pamela.tools.belief-state-planner.planexporter :as pexp])
  (:import (java.text SimpleDateFormat)
           (java.util Date))
  (:refer-clojure :exclude [rand rand-int rand-nth])
  (:gen-class))

;;;(in-ns 'pamela.tools.belief-state-planner.cli)

;(def default-action "observe") ; Maintain a belief state given a model and observations

(defonce sdf (SimpleDateFormat. "yyyy-MMdd-HHmm"))
(def received-count 0)

(def repl true)
(defonce last-ctag nil)

(def cli-options [["-m" "--model pm" "pamela model, in ir-json, of system" :default nil]
                  ["-R" "--root name" "Root pClass" :default "main"]
                  ["-g" "--goals gm" "goal definitions and support, in, ir-json" :default nil]
                  ["-G" "--groot name" "Root pClass of the goal" :default "Main"]
                  ["-s" "--samples n" "Number of samples" :default "1000"]
                  ["-d" "--maxdepth n" "Maximum search depth" :default "20"]
                  ["-r" "--rawp bool" "raw solutions? (otherwise) compiled)" :default "true"]
                  ["-o" "--output file" "output" :default ""]
                  ["-P" "--propositions file" "File containing propositions to load" :default nil]
                  ["-h" "--host rmqhost" "RMQ Host" :default "localhost"]
                  ["-p" "--port rmqport" "RMQ Port" :default 5672]
                  ["-e" "--exchange name" "RMQ Exchange Name" :default "tpn-updates"]
                  ["-b" "--dmcpid id" "DMCP ID" :default "dmcp1"]
                  ["-w" "--watchedplant id" "WATCHEDPLANT ID" :default nil]
                  ["-t" "--tracefile file" " Trace filename" :default nil]
                  ["-v" "--verbose level" "Verbose mode" :default "0"]
                  ["-T" "--threads n" "Maximum number of threads to use (0 means as many as possible)" :default "0"]
                  ["-?" "--help"]
                  ])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Commands

(def rmq-channel nil)
(def exchange nil)
(def dmcpid nil)
(def watchedplant nil)
(def running-activities nil)
(def timeoutmilliseconds 20000) ; 30 second timeout
(def tracefilename nil)
(def exitmainprogram false)

(defn test-for-termination
  [act]
  (let [now (System/currentTimeMillis)
        [plid partid fname ts fn test] act]
    (if (> (- now ts) timeoutmilliseconds)
      (do (println "Timed out: " plid partid fname) true)
      (test))))

(defn finish-activity
  [act]
  (let [[plid partid fname ts fn test] act]
    (println "Finishing " plid partid fname)
    (fn)))

(defn check-for-satisfied-activities
  []
  (let [acts running-activities]
    (def running-activities nil)
    (doseq [act acts]
      (if (test-for-termination act)
        (finish-activity act)
        (def running-activities (concat running-activities (list act)))))
    (if (not (nil? running-activities)) (println "Running-activities = " running-activities))))

(defn add-running-activity
  [act]
  (def running-activities (concat running-activities (list act)))
  (println "Running-activities = " running-activities)
  (check-for-satisfied-activities))

(defn get-field-value
  "Return the value of the specified field."
  [cmdmap]
  (let [myid (:plant-id cmdmap)
        id (:id cmdmap)
        partid (nth (:args cmdmap) 0)
        fieldname (nth (:args cmdmap) 1)]
    (if (not (and partid fieldname))
      (println "get-field-value: bad call: " cmdmap)
      (let [value (rtm/get-field-value partid fieldname)
            startobj {:state "started",
                      :id id,
                      :plant-id dmcpid }
            obj {:state "finished",
                 :plant-id dmcpid,
                 :id id,
                 :reason {:finish-state "success",
                          :field-name fieldname,
                          :value value}}]
        #_(println "get: " partid "->" fieldname "=" value)
        #_(println "About to publish: " obj " to  observations, " rmq-channel ", " exchange)
        (mq/publish-object startobj "observations" rmq-channel exchange)
        (mq/publish-object obj "observations" rmq-channel exchange)
        ))))

#_(defn set-field-value
  "Return the value of the specified field."
  [cmdmap]
  (let [partid (:plant-id cmdmap)
        fieldname (nth (:args cmdmap) 0)
        value (:value cmdmap)
        obj {:function-name "set-field-value",
                 :id "dance",
                 :state "finished",
                 :plant-id "dance-testbed",
                 :plant-part partid,
                 :field-name fieldname,
                 :observation value}]
    (if (not (and partid fieldname))
      (println "set-field-value: bad call: " cmdmap)
      (let [value (rtm/set-field-value! partid fieldname value)]
        #_(println "set: " partid "->" fieldname "=" value)
        #_(println "About to publish: " obj " to  observations, " rmq-channel ", " exchange)
        (mq/publish-object obj "observations" rmq-channel exchange)
        ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn incoming-msgs [_ metadata ^bytes payload]
  (def received-count (inc received-count))
  (when (zero? (mod received-count 1000))
    (println "Messages received so far" received-count)
    )
  (let [st (String. payload "UTF-8")
        m (tpn.fromjson/map-from-json-str st)]
    #_(println "Meta")
    #_(clojure.pprint/pprint metadata)
    #_(println "--- from exchange:" (:exchange metadata) ",routing-key:" (:routing-key metadata))
    #_(clojure.pprint/pprint m)
    #_(println "raw-data," (System/currentTimeMillis) "," st)
    (let [rk (:routing-key metadata)
          command (keyword (get m :function-name))
          observations (get m :observations)
          plantid (get m :plant-id)]
      (cond
        ;; Handle commands from the dispatcher to DMCP directly
        (and (= rk dmcpid))     (condp = command
                                 :get-field-value (get-field-value m)
                                 ;; :set-field-value (set-field-value m)
                                 (println "Unknown command received: " command m))

        ;; Handle observations from everywhere
        (= rk "observations")    (if (= plantid :plant) ;+++ we need a plant id to be unique to the camera +++
                                   nil ;; +++(recobs/process-visual-observation m)
                                   (doseq [anobs observations]
                                     (let [field (get anobs :field)
                                           value (get anobs :value)]
                                       (cond (and field value)
                                             (rtm/set-field-value! plantid field value)
                                             :else
                                             (do
                                               (println "Received observation: " anobs))))))

        ;; Handle observations from the vision system
        ;;(= rk "cart-vision")   (recobs/process-visual-observation m)

        ;; Track activities started by the dispatcher
        (= rk watchedplant)        (let [id (get m :id)
                                         plid (get m :plant-id)
                                         partid (get m :plant-part)
                                         state (get m :state)
                                         fname (get m :function-name)
                                         ts (get m :timestamp)]
                                     (if fname
                                       (if (= state :start)
                                         (do
                                           (println "function: " fname " id: " id " starting.")
                                           ;; handle the startup
                                           (let [startobj {:state "started",
                                                           :id id,
                                                           :plant-id plid }
                                                 obj {:state "finished",
                                                      :plant-id plid,
                                                      :id id,
                                                      :reason {:finish-state "success"}}]
                                             (println "About to publish: " startobj " to  observations, " rmq-channel ", " exchange)
                                             (mq/publish-object startobj "observations" rmq-channel exchange)
                                             (add-running-activity [plid
                                                                    partid
                                                                    fname
                                                                    ts
                                                                    (fn []
                                                                      (println "About to publish: " obj " to  observations, " rmq-channel ", " exchange)
                                                                      (mq/publish-object obj "observations" rmq-channel exchange))
                                                                    nil ;; +++ (recobs/postcondition plid partid fname)
                                                                    ])))
                                         (println "function: " fname " id: " id " state: " state)))))
      (check-for-satisfied-activities))))

(defn observe-plant
  "Track the the belief state of the currently oaded model"
  [& args]
  (.write *out* (format "%nIn observe-plant with: %s%n" args)))

(defn make-offline-plan
  "Track the the belief state of the currently oaded model"
  [& args]
  (.write *out* (format "%nIn observe-plant with: %s%n" args)))

(def #^{:added "0.1.0"}
  actions
  "Valid dmcp command line actions"
  {"observe" (var observe-plant)
   "make-plan" (var make-offline-plan)})

(defn usage
  "Print dmcp command line help."
  {:added "0.1.0"}
  [options-summary]
  (->> (for [a (sort (keys actions))]
         (str "  " a "\t" (:doc (meta (get actions a)))))
    (concat [""
             "dmcp"
             ""
             "Usage: dmcp [options] action"
             ""
             "Options:"
             options-summary
             ""
             "Actions:"])
    (string/join \newline)))

(defn montecarloplanner
  "DOLL Monte-Carlo Planner"
  [& args]
  ;;(println args)
  ;;(println cli-options)
  (let [parsed (cli/parse-opts args cli-options)
        {:keys [options arguments error summary]} parsed
        {:keys [help version verbose observe connect make-plan] } options
        cmd (first arguments)
        verbosity (read-string (get-in parsed [:options :verbose]))
        goals (get-in parsed [:options :goals])
        model (get-in parsed [:options :model])
        root (symbol (get-in parsed [:options :root]))
        groo (symbol (get-in parsed [:options :groot]))
        samp (read-string (get-in parsed [:options :samples]))
        maxd (read-string (get-in parsed [:options :maxdepth]))
        maxt (read-string (get-in parsed [:options :threads]))
        rawp (read-string (get-in parsed [:options :rawp]))
        outfile (get-in parsed [:options :output])
        prop (get-in parsed [:options :propositions])
        ;; For connectivity with another RMQ system
        ch-name (get-in parsed [:options :exchange])
        _ (if (> verbosity 2) (println [ "ch-name = " ch-name]))
        host (get-in parsed [:options :host])
        _ (if (> verbosity 2) (println ["host = " host]))
        exch (get-in parsed [:options :exchange])
        myid (get-in parsed [:options :dmcpid])
        wpid (get-in parsed [:options :watchedplant])
        trfn (get-in parsed [:options :tracefile])
        port (get-in parsed [:options :port])
        _ (if (> verbosity 2) (println ["port = " port]))
        help (get-in parsed [:options :help])
        _ (if (> verbosity 2) (println ["root = " root]))
        ;; importfilestem (if desired (strip-extn model) nil) ; not clear that we need that.
        ;; model (get-in parsed [:options :model])
        _ (if (> verbosity 3) (println ["model = " model]))
        _ (do
            (def repl false)
            (when help
              (println (usage (:summary parsed)))
              (when-not repl
                (System/exit 0))))

        _ (if (> verbosity 0) (println "DOLL Monte-Carlo Generative Planner" (:options parsed)))
        ]

    (global/set-verbosity verbosity)
    (irx/set-verbosity verbosity)
    ;; Establish initial belief state
    ;; Start off in a clean state
    (rtm/unload-model)
    (bs/bs-complete-reset)
    (bs/clear-belief-state)

    (cond (>= (count arguments) 1)
          (case (keyword (first arguments))
            :observe
            :NYI

            :connect
            (let [connection (rmq/connect {:host host :port port})
                  channel (lch/open connection)
                  _ (le/declare channel ch-name "topic")
                  queue (lq/declare channel)
                  qname (.getQueue queue)
                  _ (lq/bind channel qname ch-name {:routing-key "#"})
                  ctag (lc/subscribe channel qname incoming-msgs {:auto-ack true})]

              (def rmq-channel channel)
              (def exchange exch)
              (def dmcpid myid)
              (def watchedplant wpid)
              (def tracefilename trfn)
              (println "RabbitMQ connection Established")
              ;; Then what !!!*****
              (when last-ctag
                (mq/cancel-subscription (first last-ctag) (second last-ctag)))
              ;; conj for list pushes to the front, so we push channel then ctag.
              ;; So, we get ctag = (first last-ctag), and channel = (second last-ctag)
              (def last-ctag (conj last-ctag channel ctag))

              (if-not (nil? tracefilename)
                (with-open [ostrm (clojure.java.io/writer tracefilename)]
                  ;; (recobs/set-trace-stream ostrm)
                  (while (not exitmainprogram) (Thread/sleep 1000))))
              ctag)


            :make-plan
            (do
              (set-random-seed! 666) ; for repeatability of the tests
              (if model
                (do
                  (if (.exists (io/file model))
                    (do
                      (rtm/load-model model root) ; no args
                      (rtm/establish-connectivity-propositions root)
                      (rtm/establish-part-of-propositions root)
                      (if (> verbosity 3)
                        (do (rtm/describe-current-model)
                            (bs/describe-belief-state)
                            (println "")))
                      (if (> verbosity 0) (println "model loaded: " model)))
                    (do
                      (println "File does not exist: " model)
                      (Thread/sleep 2000)
                      (System/exit 1)))))
              (if goals
                (do
                  (if (.exists (io/file goals))
                    (do
                      (rtm/load-model goals groo) ; no args
                      (rtm/establish-connectivity-propositions groo)
                      (rtm/establish-part-of-propositions groo)
                      (if prop
                        (if (.exists (io/file prop))
                          (rtm/assert-propositions (read-string (slurp prop)))
                          (println "Propositions file: " prop " does not exist.")))
                      (if (> verbosity 0)
                        (do (rtm/describe-current-model)
                            (bs/describe-belief-state)
                            (println "")))
                      (if (> verbosity 0) (println "goal model loaded: " goals)))
                    (do
                      (println "File does not exist: " goals)
                      (Thread/sleep 2000)
                      (System/exit 1)))
                  (let [solutions ; (if (= maxt 1)
                        ;;  (core/solveit :samples samp :max-depth maxd :rawp true) ;+++ was rawp
                        ;; (println "maxt=" maxt)
                        (time (core/mpsolveit :samples samp :max-depth maxd :rawp true :usethreads (if (= maxt 0) :maximum maxt)))]
                    (if (not rawp)
                      (let [pamela-solutions (into #{} (map bir/compile-actions-to-pamela solutions))
                            result (case (count pamela-solutions)
                                     0 "No solutions found"
                                     1 (first (into [] pamela-solutions))
                                     (cons 'choose (map (fn [asoln] (list 'choice asoln)) pamela-solutions)))]
                        (if (= outfile "")
                          (pprint result)
                          (spit outfile (with-out-str (pprint result)))))
                      (let [pamela-solutions (into #{} (map bir/compile-actionlist-to-pamela solutions))
                            result (case (count pamela-solutions)
                                     0 ["No solutions found"]
                                     (pexp/assemble-solutions pamela-solutions groo 'goal))]
                        (if (= outfile "")
                          (pprint result)
                          (spit outfile (with-out-str (pprint (first result)))))))))
                (println "Nothing to do, no goals provided")))

            (println "Unknown action: " (first arguments)))

          :otherwise
          (println "No action specified, try: make-plan"))))

(defn  -main
  "dmcp"
  {:added "0.1.0"}
  [& args]
  (apply montecarloplanner args))

;;; (def repl true)
;;; (montecarloplanner  "-g" "test/planner/40_dcrypps2test.ir.json" "-G" "AttackPlanner" "-v" "0" "-d" "20" "-s" "1000" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_dcryppstest.ir.json" "-G" "AttackPlanner" "-v" "0" "-d" "20" "-s" "1000" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_simple.ir.json" "-G" "world" "-v" "0" "-d" "20" "-s" "1" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_simple.ir.json" "-G" "world" "-v" "0" "-d" "20" "-s" "1" "-r" "false" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_plannertest.ir.json" "-G" "world" "-v" "4" "-d" "20" "-s" "1000" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_ritatest.ir.json" "-G" "Main" "-v" "2" "-d" "50" "-P" "test/planner/40_ritatest.ppr" "-s" "1" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_ritatest.ir.json" "-G" "Main2" "-v" "2" "-d" "50" "-P" "test/planner/40_ritatest.ppr" "-s" "1" "-r" "true" "make-plan")
;;; (montecarloplanner  "-g" "test/planner/40_ritatest.ir.json" "-G" "Main3" "-v" "0" "-d" "50" "-P" "test/planner/40_ritatest.ppr" "-s" "1" "-r" "true" "make-plan")
