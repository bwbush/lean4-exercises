
open Classical


variable (α : Type) (p q : α → Prop)

variable (r : Prop)


example : (∃ x : α, r) → r :=
  λ h : ∃ x : α, r =>
    Exists.elim h
      (
        λ y : α =>
          λ hr : r =>
            hr
      )
example : (∃ x : α, r) → r :=
  λ h : ∃ x : α, r =>
    match h with
    | ⟨y, hr⟩ => hr
example : (∃ x : α, r) → r :=
  λ ⟨y, hr⟩ => hr


example (a : α) : r → (∃ x : α, r) :=
  λ hr : r =>
    Exists.intro a hr
example (a : α) : r → (∃ x : α, r) :=
  λ hr : r =>
    ⟨a, hr⟩


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (
      λ h : (∃ x, p x ∧ r) =>
        ⟨
          match h with
          | ⟨y, h'⟩ => ⟨y, h'.left⟩
        , match h with
          | ⟨y, h'⟩ => h'.right
        ⟩
    )
    (
      λ h : (∃ x, p x) ∧ r =>
        match h.left with
        | ⟨y, hp⟩ =>
            ⟨y, ⟨hp, h.right⟩⟩
    )


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (
      λ ⟨y, h⟩ =>
        Or.elim h
          (
            λ hp : p y => Or.inl ⟨y, hp⟩
          )
          (
            λ hq : q y => Or.inr ⟨y, hq⟩
          )
    )
    (
      λ h : (∃ x, p x) ∨ (∃ x, q x) =>
        Or.elim h
          (
            λ ⟨y, hp⟩ => ⟨y, Or.inl hp⟩
          )
          (
            λ ⟨y, hq⟩ => ⟨y, Or.inr hq⟩
          )
    )



example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (
      λ h : ∀ x, p x =>
        show ¬(∃ x, ¬ p x) from
          λ ⟨y, hnp⟩ =>
            suffices hp : p y from hnp hp
            show p y from h y
    )
    (
      λ h : ¬(∃ x, ¬ p x) =>
        λ y : α =>
          show p y from
            byContradiction
              (
                λ hnp : ¬ p y =>
                  h ⟨y, hnp⟩
              )
    )


example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (
      λ ⟨x, hp⟩ =>
        show ¬(∀ x, ¬ p x) from
          λ hnp : ∀ x, ¬ p x =>
            (hnp x) hp
    )
    (
      λ h : ¬(∀ x, ¬ p x) =>
        show ∃ x, p x from
          byContradiction
            (
              λ h' : ¬ ∃ x, p x =>
                have hnp : ∀ x, ¬ p x :=
                  λ y : α =>
                    byContradiction
                      (
                        λ hnnp : ¬ ¬ p y =>
                          have hp : p y := byContradiction (λ hnp' : ¬ p y=> absurd hnp' hnnp)
                          have h'' : ∃ x, p x := ⟨y, hp⟩
                          show False from h' h''
                      )
                show False from
                  h hnp
            )
    )


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (
      λ h : ¬ ∃ x, p x =>
        λ y : α =>
          byCases
            (
              λ hp : p y =>
                False.elim (h ⟨y, hp⟩)
            )
            id
    )
    (
      λ hnp : ∀ x, ¬ p x =>
        show ¬ ∃ x, p x from
          λ ⟨y, hp⟩ =>
            (hnp y) hp
    )


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (
      λ h : ¬ ∀ x, p x =>
        show ∃ x, ¬ p x from
          byContradiction
          (
            λ h' : ¬ (∃ x, ¬ p x) =>
              have hn : ∀ x, p x :=
                λ y : α =>
                  byContradiction
                    (
                      λ hnp : ¬ p y =>
                        have hn' : ∃ x, ¬ p x :=
                          ⟨y, hnp⟩
                        False.elim (h' hn')
                    )
              h hn
          )
    )
    (
      λ h : ∃ x, ¬ p x =>
        match h with
        | ⟨y, hnp⟩ =>
            show ¬ ∀ x, p x from
              λ h' : ∀ x, p x =>
                hnp (h' y)
    )



example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (
      λ h : ∀ x, p x → r =>
        λ ⟨y, hp⟩ =>
          have h' : p y → r := h y
          h' hp

    )
    (
      λ h : (∃ x, p x) → r =>
        λ x : α =>
          λ hp : p x =>
            h ⟨x, hp⟩
    )


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (
      λ ⟨x, h⟩ =>
        λ h' : ∀ y, p y =>
          h (h' x)
    )
    (
      λ h : (∀ x, p x) → r =>
        show ∃ x, p x → r from
          byCases
            (
              λ h' : ∀ x, p x =>
                have hr : r := h h'
                ⟨a, λ _ => hr⟩
            )
            (
              λ h' : ¬ ∀ x, p x =>
                show ∃ x, p x → r from
                  byContradiction
                    (
                      λ hn'' : ¬ ∃ x, p x → r =>
                        have hp : ∀ x, p x :=
                          λ y : α =>
                            byContradiction
                              (
                                λ hnp : ¬ p y =>
                                  have h'' : ∃ x, p x → r :=
                                    ⟨y, λ hp : p y => False.elim (hnp hp)⟩
                                  False.elim (hn'' h'')
                              )
                        h' hp
                    )
            )
    )


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (
      λ ⟨x, h⟩ =>
        λ hr : r =>
          ⟨x, h hr⟩
    )
    (
      λ h : r → ∃ x, p x =>
        show ∃ x, r → p x from
          Or.elim (em r)
            (
              λ hr : r =>
                have ⟨y, hp⟩ := h hr
                ⟨y, λ hr' : r => hp⟩
            )
            (
              λ hnr : ¬r => ⟨a, λ hr : r => False.elim (hnr hr)⟩
            )
    )
