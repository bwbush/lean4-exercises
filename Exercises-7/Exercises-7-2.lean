
namespace Ex


-- 7.2 Define some operations on lists like `length` and `reverse`.

inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α


open Ex.List

def list123 := cons 1 (cons 2 (cons 3 nil))
def list456 := cons 3 (cons 5 (cons 6 nil))
def list654 := cons 6 (cons 5 (cons 4 nil))
def list123456 := cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons 6 nil)))))


def length (s : List α) : Nat :=
  match s with
  | nil       => 0
  | cons _ s' => 1 + length s'

example : length (nil : List α) = 0 := rfl

example : length list123 = 3 := rfl


def append (s t : List α) : List α :=
  match s with
  | nil       => t  
  | cons x s' => cons x (append s' t)

--example : append list123 list456 = list123456 := by
--  simp [cons_append]


def reverse (s : List α) : List α :=
  match s with
  | nil       => nil
  | cons x s' => append (reverse s') (cons x nil)


-- 7.2.a. `length (s ++ t) = length s + length t`

theorem length_nil : length (nil : List α) = 0 := rfl

theorem length_cons (s : List α) : length (cons x s) = 1 + length s := rfl

theorem cons_append (s t : List α) : append (cons x s) t = cons x (append s t) := rfl

theorem nil_append (s : List α) : append nil s = s := rfl

theorem append_nil (s : List α) : append s nil = s := by
  induction s with
  | nil          => rfl
  | cons x s' ih => rw [cons_append, ih]

theorem length_append (s t : List α) : length (append s t) = length s + length t := by
  induction s with
  | nil          => rw [nil_append, length_nil, Nat.zero_add]
  | cons x s' ih => rw [cons_append, length_cons, length_cons, Nat.add_assoc, ih]


-- 7.2.b. `length (reverse t) = length t`

theorem reverse_cons (x : α) (s : List α) : reverse (cons x s) = append (reverse s) (cons x nil) := by
  induction s with
  | nil           => rfl
  | cons x' s' ih => rfl

theorem length_reverse (s : List α) : length (reverse s) = length s := by
  induction s with
  | nil          => rfl
  | cons x s' ih => rw [length_cons, reverse_cons, length_append, ih, length_cons, length_nil, Nat.add_zero, Nat.add_comm]


-- 7.2.c. `reverse (reverse t) = t`

theorem reverse_nil : reverse (nil : List α) = (nil : List α) := rfl

theorem append_assoc (s t u : List α) : append s (append t u) = append (append s t) u := by
  induction s with 
  | nil          => rw [nil_append, nil_append]
  | cons x s' ih => rw [cons_append, ih, cons_append, cons_append]

theorem reverse_append (s t : List α) : reverse (append s t) = append (reverse t) (reverse s) := by
  induction s with
  | nil          => rw [nil_append, reverse_nil, append_nil]
  | cons x s' ih => rw [cons_append, reverse_cons, ih, reverse_cons, append_assoc]

theorem reverse_reverse (s : List α) : reverse (reverse s) = s := by
  induction s with
  | nil          => rfl
  | cons x s' ih => rw [reverse_cons, reverse_append, ih, reverse_cons, reverse_nil, nil_append, cons_append, nil_append]
