
variable (α : Type) (p q : α → Prop)


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (
      λ h : ∀ x, p x ∧ q x =>
          ⟨
            λ y : α =>
              (h y).left
          , λ y : α =>
              (h y).right
          ⟩
    )
    (
      λ h : (∀ x, p x) ∧ (∀ x, q x) =>
        λ y : α =>
          ⟨
            h.left y
          , h.right y
          ⟩
    )


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ h : ∀ x, p x → q x =>
    λ h' : ∀ y, p y =>
      λ z : α =>
        have h'' : p z → q z := h z
        have z' : p z := h' z
        h'' z'


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ h : (∀ x, p x) ∨ (∀ x, q x) =>
    λ y : α =>
      Or.elim h
        (
          λ hl : ∀ x, p x =>
            Or.inl (hl y)
        )
        (
          λ hr : ∀ x, q x =>
            Or.inr (hr y)
        )
