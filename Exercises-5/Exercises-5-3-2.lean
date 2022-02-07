
open Classical


variable (p q r s : Prop)


example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := by
  intro (h : p → r ∨ s)
  . apply Or.elim (em r)
    . intro hr
      apply Or.inl
      intro hp
      assumption
    . intro hnr
      apply Or.inr
      intro hp
      apply Or.elim (h hp)
      . intro hr; contradiction
      . intro hs; assumption


example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  apply Or.elim (em p)
  . intro hp
    apply Or.inr
    intro hq
    exact h ⟨hp, hq⟩
  . apply Or.inl


example : ¬(p → q) → p ∧ ¬q := by
  intro h
  constructor
  . apply Or.elim (em p)
    . intro hp
      assumption
    . intro hnp
      apply False.elim
      apply h
      intro hnp
      contradiction
  . intro hq
    apply h (λ hp => hq)


example : (p → q) → (¬p ∨ q) := by
  intro h
  apply Or.elim (em p)
  . intro hp
    apply Or.inr
    exact h hp
  . apply Or.inl


example : (¬q → ¬p) → (p → q) := by
  intro h
  intro hp
  match em q with
  | Or.inl hq =>
    assumption
  | Or.inr hnq =>
    have hnp := h hnq
    contradiction


example : p ∨ ¬p := by
  exact em p


example : (((p → q) → p) → p) := by
  intro h
  apply Or.elim (em p)
  . apply id
  . intro hnp
    apply h
    intro hp
    contradiction
    