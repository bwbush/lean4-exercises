
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | constructor) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)


example (p q r s : Prop) (hp : p) : (p ∨ q ∨ r ∨ s) ∧ (q ∨ s ∨ p ∨ r) ∧ (s ∨ q ∨ r ∨ p) := by
  repeat (first | constructor) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)


example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor
  . apply Or.inl
    assumption
  . constructor
    . apply Or.inr
      apply Or.inl
      assumption
    . apply Or.inr
      apply Or.inr
      assumption


example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor
  any_goals constructor
  any_goals (repeat (first | apply Or.inl; assumption | apply Or.inr | assumption))

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> try constructor <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (first | constructor) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor
  . repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
  . constructor
    . repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
    . repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : (q ∨ p ∨ r) := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

example (p q r : Prop) (hp : p) : (q ∨ r ∨ p) := by
  repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
