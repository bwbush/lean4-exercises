
open Classical


variable (p q r s : Prop)


example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
  λ h : p → r ∨ s =>
    Or.elim (em r)
      (
        λ hr : r =>
          Or.inl
            (
              λ hp : p => hr
            )
      )
      (
        λ hnr : ¬r =>
          Or.inr
            (
              λ hp : p =>
                Or.elim (h hp)
                  (λ hr : r => absurd hr hnr)
                  (λ hs : s => hs)
            )
      )


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ h : ¬(p ∧ q) =>
    Or.elim (em p)
      (
        λ hp : p =>
          Or.inr
            (λ hq : q => h ⟨hp, hq⟩)
      )
      Or.inl


example : ¬(p → q) → p ∧ ¬q :=
  λ h : ¬(p → q) =>
    ⟨
      Or.elim (em p)
        (λ hp : p => hp)
        (
          λ hnp : ¬p =>
            False.elim (h (λ hp : p => absurd hp hnp))
        )
    , λ hq : q =>
        show False
        from h (λ hp : p => hq)
    ⟩


example : (p → q) → (¬p ∨ q) :=
  λ h : p → q =>
    Or.elim (em p)
      (
        λ hp : p =>
          Or.inr (h hp)
      )
      Or.inl


example : (¬q → ¬p) → (p → q) :=
  λ h : ¬q → ¬p =>
    λ hp : p =>
      Or.elim (em q)
        (λ hq : q => hq)
        (λ hnq : ¬q => absurd hp (h hnq))


example : p ∨ ¬p := em p


example : (((p → q) → p) → p) :=
  λ h : (p → q) → p =>
    Or.elim (em p)
      (
        λ hp : p =>
          hp
      )
      (
        λ hnp : ¬p =>
          h (λ hp : p => absurd hp hnp)
      )
