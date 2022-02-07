
variable (men : Type) (barber : men)

variable  (shaves : men → men → Prop)


example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have h' := h barber
  have hnb := λ hs => (h'.mp hs) hs
  have hb := h'.mpr hnb
  contradiction
