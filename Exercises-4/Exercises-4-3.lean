
variable (men : Type) (barber : men)

variable  (shaves : men → men → Prop)


example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let s : Prop := shaves barber barber
  have h' : s ↔ ¬ s := h barber
  show False from
    have h'' : ¬s :=
      λ hs : s => (h'.mp hs) hs
    h'' (h'.mpr h'')

