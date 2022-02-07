
variable (p q r : Prop)


-- commutativity of ∧ and ∨


example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left
  . intro h
    apply And.intro
    . case left => exact h.right
    . apply h.left


example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    . cases h with
      | inl hp => apply Or.inr; exact hp
      | inr hq => apply Or.inl; assumption
  . intro h
    . cases h
      . apply Or.inr
        assumption
      . apply Or.inl; assumption
    

-- associativity of ∧ and ∨


example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro h
    . constructor
      . exact h.left.left
      . constructor
        . exact h.left.right
        . exact h.right
  . intro h
    cases h with
    | intro hp hqr =>
      cases hqr
      repeat (first | constructor | assumption)


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hpq =>
      cases hpq with
      | inl hp => apply Or.inl; assumption
      | inr hq => apply Or.inr; apply Or.inl; assumption
    | inr hr => apply Or.inr; apply Or.inr; assumption
  . intro
    | Or.inl hp => apply Or.inl; apply Or.inl; assumption
    | Or.inr hqr =>
      match hqr with
      | Or.inl hq => apply Or.inl; apply Or.inr; assumption
      | Or.inr hr => apply Or.inr; assumption


-- distributivity


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro
    | ⟨hp, Or.inl hq⟩ => repeat (first | constructor | assumption)
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; constructor; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro
    | Or.inl hp => repeat (first | constructor | assumption)
    | Or.inr ⟨hq, hr⟩ => constructor; apply Or.inr; assumption; apply Or.inr; assumption
  . intro
    | ⟨Or.inl hp, _⟩ => constructor; assumption
    | ⟨Or.inr _, Or.inl hp⟩ => constructor; assumption
    | ⟨Or.inr hq, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption


-- other properties


example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h
    . intro
      | ⟨hp, hq⟩ => exact (h hp) hq
  . intro h
    . intro hp
      intro hq
      apply h; constructor <;> assumption


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h
    . constructor
      . intro | hp => exact h (Or.inl hp)
      . intro | hq => apply h; apply Or.inr; assumption
  . intro
    | ⟨hpr, hqr⟩ =>
      intro
      | Or.inl hp => exact hpr hp
      | Or.inr hq => exact hqr hq


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h
    constructor
    . intro | hp => apply h; apply Or.inl; assumption
    . intro | hq => apply h (Or.inr hq)
  . intro
    | ⟨hnp, hnq⟩ =>
      intro
      | Or.inl (hp : p) => exact hnp hp
      | Or.inr hq => contradiction


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  . intro
    | ⟨hp, hq⟩ =>
      match h with
      | Or.inl hnp => contradiction
      | Or.inr hnq => contradiction


example : ¬(p ∧ ¬p) := by
  intro | ⟨hp, hnp⟩ => contradiction


example : p ∧ ¬q → ¬(p → q) := by
  intro
    | ⟨hp, hnq⟩ =>
      intro h
      have hq := h hp
      contradiction


example : ¬p → (p → q) := by
  intro | hnp => intro | hp => contradiction


example : (¬p ∨ q) → (p → q) := by
  intro h
  . intro hp
    match h with
    | Or.inl hnp => contradiction
    | Or.inr hq => assumption


example : p ∨ False ↔ p := by
  constructor
  . intro
    | Or.inl hp => assumption
    | Or.inr False => contradiction
  . apply Or.inl


example : p ∧ False ↔ False := by
  constructor
  . intro
    | ⟨_, False⟩ => contradiction
  . apply False.elim


example : (p → q) → (¬q → ¬p) := by
  intro h
  . intro hnq
    intro hp
    exact hnq (h hp)
