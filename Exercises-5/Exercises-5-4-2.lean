
variable (α : Type) (p q : α → Prop)
variable (r : Prop)


example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  constructor
  . intro har
    apply har
    assumption
  . intro hr
    intro y
    assumption


open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    match em r with
    | Or.inl hr => apply Or.inr; assumption
    | Or.inr hl =>
      apply Or.inl
      intro y
      match h y with
      | Or.inl hp => assumption
      | Or.inr hr => contradiction
  . intro h
    intro y
    match h with
    | Or.inl h' => apply Or.inl; exact h' y
    | Or.inr hr => apply Or.inr; assumption


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h
    intro hr
    intro y
    apply h y
    assumption
  . intro h
    intro y
    intro hr
    exact (h hr) y
