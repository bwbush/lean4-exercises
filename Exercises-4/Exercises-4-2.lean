
variable (α : Type) (p q : α → Prop)
variable (r : Prop)


example : α → ((∀ x : α, r) ↔ r) :=
  λ x : α =>
    Iff.intro
      (
        λ hr : ∀ x : α, r =>
          hr x
      )
      (
        λ hr : r =>
          λ y : α => hr
      )


open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (
      λ h : ∀ x, p x ∨ r =>
        Or.elim (em r)
          Or.inr
          (
            λ hnr : ¬r =>
              Or.inl
                (
                  λ y : α =>
                    Or.elim (h y)
                      (
                        λ hp : p y => hp
                      )
                      (
                        λ hr : r => absurd hr hnr
                      )
                )
          )
    )
    (
      λ h : (∀ x, p x) ∨ r =>
        λ y : α =>
          Or.elim h
            (
              λ h' : ∀ x, p x =>
                Or.inl (h' y)
            )
            (
              λ hr : r => Or.inr hr
            )
    )


example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (
      λ h : ∀ x, r → p x =>
        λ hr : r =>
          λ y : α =>
            (h y) hr
    )
    (
      λ h : r → ∀ x, p x =>
        λ y : α =>
          λ hr : r =>
            (h hr) y
    )
