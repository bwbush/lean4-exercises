
variable (α : Type) (p q : α → Prop)


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro y
      match h y with
      | ⟨hp, _⟩ => assumption
    . intro y
      match h y with
      | ⟨_, hq⟩ => assumption
  . intro h
    intro y
    match h with
    | ⟨hp, hq⟩ => exact ⟨hp y, hq y⟩


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro hapq
  intro hap
  intro z
  have hpq := hapq z
  have hp := hap z
  exact hpq hp


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  intro y
  match h with
  | Or.inl hl => apply Or.inl; exact hl y
  | Or.inr hr => apply Or.inr; exact hr y
