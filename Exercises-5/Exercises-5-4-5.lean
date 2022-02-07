
open Classical


variable (α : Type) (p q : α → Prop)

variable (r : Prop)


example : (∃ x : α, r) → r := by
  intro ⟨y, hr⟩
  assumption


example (a : α) : r → (∃ x : α, r) := by
  intro hr
  constructor <;> assumption


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro h
    constructor
    . match h with
      | ⟨y, ⟨hp, _⟩⟩ => constructor <;> assumption
    . match h with
      | ⟨_, ⟨_, hr⟩⟩ => assumption
  . intro ⟨⟨y, hp⟩, hr⟩
    constructor; any_goals constructor; any_goals assumption


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro
    | ⟨y, Or.inl hp⟩ => apply Or.inl; constructor <;> assumption
    | ⟨y, Or.inr hq⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨y, hp⟩ => exact ⟨y, Or.inl hp⟩
    | Or.inr ⟨y, hq⟩ => exact ⟨y, Or.inr hq⟩



example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h
    intro ⟨y, hhp⟩
    have hp := h y
    contradiction
  . intro h
    intro y
    apply byContradiction
    intro hnp
    exact h ⟨y, hnp⟩


example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro ⟨x, hp⟩
    show ¬(∀ x, ¬ p x)
    intro hnp
    have hnp' := hnp x
    contradiction
  . intro h
    apply byContradiction
    intro h'
    have hnp : ∀ x, ¬ p x := by
      intro y
      match em (¬ p y) with
      | Or.inl hnp' => assumption
      | Or.inr hnnp =>
        have hp : p y := by
          apply byContradiction
          intro hnp'
          contradiction
        have h'' : ∃ x, p x := ⟨y, hp⟩
        contradiction
    contradiction


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro h
    intro y
    match em (p y) with
    | Or.inl hp =>
      have h' : ∃ x, p x := ⟨y, hp⟩
      contradiction
    | Or.inr hnp => assumption
  . intro hnp
    show ¬ ∃ x, p x
    intro ⟨y, hp⟩
    have hnp' := hnp y
    contradiction


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . intro h
    apply byContradiction
    intro h'
    have hn : ∀ x, p x := by
      intro y
      apply byContradiction
      intro hnp
      have hn' : ∃ x, ¬ p x := by constructor assumption
      contradiction
    contradiction
  . intro ⟨y, hnp⟩
    intro h'
    apply hnp
    apply h' y


example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h
    intro ⟨y, hp⟩
    have h' := h y
    apply h'
    assumption
  . intro h
    intro x
    intro hp
    apply h
    constructor; assumption


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro ⟨x, h⟩
    intro h'
    exact h (h' x)
  . intro h
    match em (∀ x, p x) with
    | Or.inl h' =>
      have hr := h h'
      exists a
      intro _
      assumption
    | Or.inr h' =>
      apply byContradiction
      intro hn''
      have hp : ∀ x, p x := by
        intro y
        apply byContradiction
        intro hnp
        have h'' : ∃ x, p x → r := by
          exists y
          intro hp
          contradiction
        contradiction
      contradiction


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro ⟨x, h⟩
    intro hr
    constructor
    exact h hr
  . intro h
      match em r with
      | Or.inl hr =>
        match h hr with
        | ⟨y, hp⟩ =>
          exists y
          intro hr'
          assumption
      | Or.inr hnr =>
        exists a
        intro hr
        contradiction
