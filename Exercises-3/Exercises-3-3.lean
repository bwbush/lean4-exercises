
variable (p q : Prop)


example : ¬(p ↔ ¬p) :=
  λ h : p ↔ ¬p =>
    show False from
    have h' : ¬p :=
      λ hp : p => (h.mp hp) hp
    h' (h.mpr h')
