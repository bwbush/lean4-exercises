
variable (p q r : Prop)


-- commutativity of ∧ and ∨


example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (
      λ hpq : p ∧ q =>
        have hp : p := hpq.left
        have hq : q := hpq.right
        show q ∧ p
          from And.intro hq hp
    )
    (
      λ hqp : q ∧ p =>
        have hq : q := hqp.left
        have hp : p := hqp.right
        show p ∧ q
          from And.intro hp hq
    )


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (
      λ hpq : p ∨ q =>
        Or.elim hpq
          (
            λ hp : p =>
              show q ∨ p
                from Or.inr hp
          )
          (
            λ hq : q =>
              show q ∨ p
                from Or.inl hq
          )
    )
    (
      λ hpq : q ∨ p =>
        Or.elim hpq
          (
            λ hq : q =>
              show p ∨ q
                from Or.inr hq
          )
          (
            λ hp : p =>
              show p ∨ q
                from Or.inl hp
          )
    )
    

-- associativity of ∧ and ∨


example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (
      λ h : (p ∧ q) ∧ r =>
        have hp : p := h.left.left
        have hq : q := h.left.right
        have hr : r := h.right
        show p ∧ (q ∧ r)
          from And.intro hp (And.intro hq hr)
    )
    (
      λ h : p ∧ (q ∧ r) =>
        let hp : p := h.left
        let hq : q := h.right.left
        let hr : r := h.right.right
        ⟨⟨hp, hq⟩, hr⟩
    )


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (
      λ h : (p ∨ q) ∨ r =>
        Or.elim h
          (
            λ h' : p ∨ q =>
              Or.elim h'
                (λ hp : p => Or.inl hp)
                (λ hq : q => Or.inr (Or.inl hq))
          )
          (λ hr : r => Or.inr (Or.inr hr))
    )
    (
      λ h : p ∨ (q ∨ r) =>
        Or.elim h
          (λ hp : p => Or.inl (Or.inl hp))
          (
            λ h' : q ∨ r =>
              Or.elim h'
                (λ hq : q => Or.inl (Or.inr hq))
                (λ hr : r => Or.inr hr)
          )
    )


-- distributivity


example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (
      λ h : p ∧ (q ∨ r) =>
        have hp : p := h.left
        Or.elim h.right
          (λ hq : q => Or.inl ⟨hp, hq⟩)
          (λ hr : r => Or.inr ⟨hp, hr⟩)
    )
    (
      λ h : (p ∧ q) ∨ (p ∧ r) =>
        Or.elim h
          (λ h' : p ∧ q => ⟨h'.left, Or.inl h'.right⟩)
          (λ h' : p ∧ r => ⟨h'.left, Or.inr h'.right⟩)
    )


example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (
      λ h : p ∨ (q ∧ r) =>
        Or.elim h
          (λ hp : p => ⟨Or.inl hp, Or.inl hp⟩)
          (λ h' : q ∧ r => ⟨Or.inr h'.left, Or.inr h'.right⟩)
    )
    (
      λ h : (p ∨ q) ∧ (p ∨ r) =>
        Or.elim h.left
          (λ hp : p => Or.inl hp)
          (
            λ hq : q =>
              Or.elim h.right
                (λ hp : p => Or.inl hp)
                (λ hr : r => Or.inr ⟨hq, hr⟩)
          )
    )


-- other properties


example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (
      λ h : p → (q → r) =>
        λ h' : p ∧ q =>
          (h h'.left) h'.right
    )
    (
      λ h : p ∧ q → r =>
        λ hp : p =>
          λ hq : q =>
            h ⟨hp, hq⟩
    )


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (
      λ h : (p ∨ q) → r =>
        ⟨
          λ hp : p => h (Or.inl hp)
        , λ hq : q => h (Or.inr hq)
        ⟩
    )
    (
      λ h : (p → r) ∧ (q → r) =>
        λ h' : p ∨ q =>
          Or.elim h'
            (λ hp : p => h.left hp)
            (λ hq : q => h.right hq)
    )


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (
      λ h : ¬(p ∨ q) =>
        ⟨
          λ hp : p => show False from h (Or.inl hp)
        , λ hq : q => show False from h (Or.inr hq)
        ⟩
    )
    (
      λ h : ¬p ∧ ¬q =>
        λ h' : p ∨ q =>
          Or.elim h'
            (λ hp : p => h.left hp)
            (λ hq : q => h.right hq)
    )


example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h : ¬p ∨ ¬q =>
    λ h' : p ∧ q =>
      Or.elim h
        (λ hnp : ¬p => hnp h'.left)
        (λ hnq : ¬q => hnq h'.right)


example : ¬(p ∧ ¬p) :=
  λ h : p ∧ ¬p => h.right h.left


example : p ∧ ¬q → ¬(p → q) :=
  λ h : p ∧ ¬q =>
    λ h' : p → q =>
      have hnq : ¬q := h.right
      have hq : q := h' h.left
      show False
        from hnq hq


example : ¬p → (p → q) :=
  λ hnp : ¬p =>
    λ hp : p => absurd hp hnp


example : (¬p ∨ q) → (p → q) :=
  λ h : ¬p ∨ q =>
    λ hp : p =>
      Or.elim h
        (λ hnp : ¬p => False.elim (hnp hp))
        (λ hq : q => hq)


example : p ∨ False ↔ p :=
  Iff.intro
    (
      λ h : p ∨ False =>
        Or.elim h
          (λ hp : p => hp)
          False.elim
    )
      Or.inl


example : p ∧ False ↔ False :=
  Iff.intro
    (
      λ h : p ∧ False =>
        h.right
    )
    False.elim


example : (p → q) → (¬q → ¬p) :=
  λ h : p → q =>
    λ hnq : ¬q =>
      λ hp : p =>
        absurd (h hp) hnq
