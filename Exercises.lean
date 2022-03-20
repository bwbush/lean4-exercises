
variable (p q r : Prop)

#check Eq.refl




variable (α β : Type)


example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl (f a)


example (a : α) (b : α) : (a, b).1 = a := Eq.refl a


example : 2 + 3 = 5 := Eq.refl 5




def meets₁ (x : Nat) :=
  x ≥ 3

#eval meets₁ 4

#reduce meets₁ 4

example : meets₁ 3 :=
  calc
    meets₁ 3 = 3 ≥ 3 := by rw


def is_even (a : Nat) := ∃ b, a = 2 * b

#eval is_even 2

#reduce is_even 2


example : is_even 2 :=
  Exists.intro 1
    (
      calc
        is_even 2 = 2 * 1 := by rw [is_even]
    )



  example : 2 + 1 = 3 := rfl