
(def classes
  #{
    :locations #{ :modes [:table :hand :phone]}
    :phone #{ :modes [:failed :off :on] :fields [:where :location-a :location-y]}
    :phone-back #{ :modes [] :fields [:where :location-a :location-y]}
    :battery #{ :modes [:charged :discharged :failed] :fields [:where :location-a :location-y]}
    :hand #{ :modes [] :fields [:location-x :location-y]}
    })

(def objects
  #{
    :the-phone :phone
    :battery1 :battery
    ;; :battery2 :battery
    :the-back :phone-back
    ;; :hand1 :hand
    :hand2 :hand})

(def activities
  #{
    :phone
    #{
      :remove-back-from-phone [nil nil]
      :turn-on [nil :on]
      :pick-up-from-table ['(= (field :where) (mode-of :locations :table))
                           '(= (field :where) (mode-of :locations :hand))]
      :place-on-table ['(= (field :where) (mode-of :locations :hand))
                       '(= (field :where) (mode-of :locations :table))]}
    :phone-back
    #{
      :remove-from-phone [nil '(= (field :where) (mode-of :locations :hand))]
      :place-on-table ['(= (field :where) (mode-of :locations :hand))
                       '(= (field :where) (mode-of :locations :table))]
      :pickup-from-table ['(= (field :where) (mode-of :locations :table))
                          '(= (field :where) (mode-of :locations :hand))]
      :install-into-phone ['(= (field :where) (mode-of :locations :hand))
                           '(= (field :where) (mode-of :locations :phone))]}
    :battery
    #{ :remove-from-phone ['(= (field :where) (mode-of :locations :phone))
                           '(= (field :where) (mode-of :locations :hand))]
      :place-on-table ['(= (field :where) (mode-of :locations :hand))
                       '(= (field :where) (mode-of :locations :table))]
      :pickup-from-table ['(= (field :where) (mode-of :locations :table))
                          '(= (field :where) (mode-of :locations :hand))]
      :install-into-phone ['(= (field :where) (mode-of :locations :hand))
                           '(= (field :where) (mode-of :locations :phone))]}
    :hand
    #{ }})

(defn establish-initial-belief-state
  "Given the current model, establish the belief state."
  []
  )

;;; Fin
