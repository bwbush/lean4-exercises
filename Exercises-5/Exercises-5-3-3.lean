
variable (p q : Prop)


example : ¬(p ↔ ¬p) := by
  intro h
  have hnp := λ hp => (h.mp hp) hp
  have hp := h.mpr hnp
  contradiction
