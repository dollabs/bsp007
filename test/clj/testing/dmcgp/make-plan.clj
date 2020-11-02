;; Copyright © 2016 Dynamic Object Language Labs Inc.
;;
;; This software is licensed under the terms of the
;; Apache License, Version 2.0 which can be found in
;; the file LICENSE at the root of this distribution.

;; Acknowledgement and Disclaimer:
;; This material is based upon work supported by the Army Contracting
;; and DARPA under contract No. W911NF-15-C-0005.
;; Any opinions, findings and conclusions or recommendations expressed
;; in this material are those of the author(s) and do necessarily reflect the
;; views of the Army Contracting Command and DARPA.

(ns testing.dmcgp.make-plan
  (:require [clojure.test :refer :all]
            [clojure.string :as string]
            [environ.core :refer [env]]
            [me.raynes.fs :as fs]
            [avenir.utils :refer [and-fn]]
            [pamela.unparser :refer :all]
            [pamela.parser :refer [parse]]
            [pamela.cli :refer [reset-gensym-generator]]
            [pamela.utils :refer [output-file]]
            [plan-schema.utils :refer [fs-get-path fs-basename]]))

#_(deftest testing-dmcgp-make-plan
  (testing "testing-dmcgp-make-plan"
    (let [excludes #{"biased-coin.pamela" ; #127 as an example

                    }
          top (fs/file (:user-dir env))
          top-path (str (fs-get-path top) "/")
          pamela (fs/file top "test" "pamela")
          regression (fs/file pamela "regression")
          test-example? (fn [path]
                          (let [filename (fs-basename path)]
                            (and (string/ends-with? filename ".pamela")
                              (not (excludes filename)))))
          examples (filter test-example?
                     (concat
                       (sort-by fs/base-name (fs/list-dir pamela))
                       (sort-by fs/base-name (fs/list-dir regression))))
          pamela-unparse (fs/file top "target" "parser" "UNPARSE")
          regression-unparse (fs/file top "target" "parser" "regression" "UNPARSE")]
      (if-not (fs/exists? pamela-unparse)
        (fs/mkdirs pamela-unparse))
      (if-not (fs/exists? regression-unparse)
        (fs/mkdirs regression-unparse))
      (doseq [example examples]
        (let [example-name (fs-basename example)
              example-path (fs-get-path example)
              regression? (string/includes? example-path "/regression/")
              example-plan-name (string/replace example-name
                                #"\.pamela$" ".plan")
              example-plan-file (fs/file (fs/parent example) "PLAN" example-plan-name)
              example-plan-path (fs-get-path example-plan-file top-path)
              example-plan (if (fs/exists? example-plan-file)
                           (read-string (slurp example-plan-path))
                           {:error (str "Rubrique does not exist: "
                                     example-plan-path)})
              specimen-plan-file (fs/file
                                 (if regression? regression-plan dmcgp-plan)
                                 example-plan-name)
              specimen-plan-path (fs-get-path specimen-plan-file top-path)
              specimen-src-file (fs/file
                                 (if regression? regression-plan dmcgp-plan)
                                 example-name)
              specimen-src-path (fs-get-path specimen-src-file top-path)
              _ (println "PLAN" example-name
                  ;; "\n  RUBRIC" example-plan-path
                  ;; "\n  SPECIMEN" specimen-plan-path
                  ;; "\n  KEYS" (keys example-plan)
                  )
              specimen-src (unparse example-plan)
              _ (output-file specimen-src-path "raw" specimen-src)
              options {:input [specimen-src-path]}
              specimen-plan (parse options)
              _ (output-file specimen-plan-path "plan" specimen-plan) ;; will sort
              specimen-ir (if (fs/exists? specimen-plan-file)
                            (read-string (slurp specimen-plan-path))
                            {:error (str "Specimen does not exist: "
                                      specimen-plan-path)})]
          ; example is expected, specimen is current.
          (is (= example-plan specimen-plan)
              (str "PLAN files should match\nExpected: " example-plan-path "\nCurrent: " specimen-plan-file)))))))
