
namespace Ex


inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

open Nat

def one := succ zero
def two := succ one
def three := succ two
def six := succ (succ (succ three))
def eight := succ (succ six)

#eval one
#eval two
#eval three
#eval six
#eval eight


def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

example : add two one = three
  := rfl

theorem add_zero (m : Nat) : add m zero = m :=
  rfl

theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) :=
  rfl

theorem zero_add (n : Nat) : add zero n = n := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [add_succ, ih]

theorem succ_add (m n : Nat) : add (succ m) n = succ (add m n) := by
  induction n with
  | zero       => rw [add_zero, add_zero]
  | succ n' ih => rw [add_succ, add_succ, ih]

theorem add_one (n : Nat) : add n one = succ n :=
  rfl

theorem one_add (n : Nat) : add one n = succ n := by
  induction n with
  | zero       => rfl
  | succ n' ih => rw [add_succ, ih]

theorem add_comm (m n : Nat) : add m n = add n m := by
  induction n with
  | zero       => rw [add_zero, zero_add]
  | succ n' ih => rw [add_succ, succ_add, ih]
  
theorem add_assoc (m n k : Nat) : add (add m n) k = add m (add n k) := by
  induction k with
  | zero       => rw [add_zero, add_zero]
  | succ k' ih => rw [add_succ, add_succ, add_succ, ih]


-- Define multiplication on naturals.

def mul (m n : Nat) : Nat :=
  match n with
  | zero        => zero
  | succ n'     => add m (mul m n')

#eval mul (succ (succ zero)) (succ (succ (succ zero)))

example : mul two three = six :=
  rfl


-- Define predecessor function on naturals.

def pred (n : Nat) : Nat :=
  match n with
  | zero          => zero
  | succ Nat.zero => zero
  | succ n'       => n'


-- Define truncated subtraction on naturals.

def sub (m n : Nat) : Nat :=
  match n with
  | zero    => m
  | succ n' => sub (pred m) n'

example : sub two one = one := rfl


-- Define exponentiation on naturals.

def exp1 (m n : Nat) : Nat :=
  match n with
  | zero    => succ zero
  | succ n' => mul (succ m) (exp1 m n')


-- Then try proving . . .


theorem mul_zero (n : Nat) : mul n zero = zero :=
  rfl

theorem mul_one (n : Nat) : mul n one = n :=
  rfl

theorem mul_succ (m n : Nat) : mul m (succ n) = add m (mul m n) :=
  rfl

theorem zero_mul (n : Nat) : mul zero n = zero := by
  induction n with
  | zero      => rfl
  | succ n ih => rw [mul_succ, zero_add, ih]

theorem one_mul (n : Nat) : mul one n = n := by
  induction n with
  | zero       => rfl
  | succ n' ih => rw [mul_succ, one_add, ih]

theorem mul_assoc (n m k : Nat) : mul k (mul m n) = mul (mul k m) n := sorry

theorem mul_dist : mul (add m n) k = add (mul m k) (mul n k) := by
  induction k with
  | zero       => rw [mul_zero, mul_zero, mul_zero, add_zero]
  | succ k' ih => calc
                    mul (add m n) (succ k') = add (add m n) (mul (add m n) k')          := by rw [mul_succ]
                    _                       = add (add m n) (add (mul m k') (mul n k')) := by rw [ih]
                    _                       = add m (add n (add (mul m k') (mul n k'))) := by rw [add_assoc]
                    _                       = add m (add n (add (mul n k') (mul m k'))) := by simp [add_comm]
                    _                       = add m (add (add n (mul n k')) (mul m k')) := by rw [add_assoc]
                    _                       = add m (add (mul n (succ k')) (mul m k'))  := by rw [← mul_succ]
                    _                       = add m (add (mul m k') (mul n (succ k')))  := by simp [add_comm]
                    _                       = add (add m (mul m k')) (mul n (succ k'))  := by rw [add_assoc]
                    _                       = add (mul m (succ k')) (mul n (succ k'))   := by rw [← mul_succ]

theorem succ_mul (m n : Nat) : mul (succ m) n = add n (mul m n) := by
  induction n with
  | zero       => rw [mul_zero, zero_add, mul_zero]
  | succ n' ih => rw [mul_succ, ih, mul_succ, succ_add, succ_add, ← add_assoc, ← add_assoc]
                  simp [add_comm]

theorem mul_comm : mul m n = mul n m := by
  induction n with
  | zero       => rw [mul_zero, zero_mul]
  | succ n' ih => rw [mul_succ, succ_mul, add_comm, ih, add_comm]

theorem mul_comm' : mul m n = mul n m := by
  induction n <;> simp [*, mul_zero, zero_mul, mul_succ, succ_mul, add_comm]


theorem succ_zero : succ zero = one := rfl

theorem pred_zero : pred zero = zero := rfl

theorem pred_one : pred one = zero := rfl

example : pred two = one := rfl

theorem pred_succ (m : Nat) : pred (succ m) = m := by
  match m with
  | zero    => rfl
  | succ m' => rfl


theorem sub_succ (m n : Nat) : sub m (succ n) = sub (pred m) n := rfl

theorem zero_sub (n : Nat) : sub zero n = zero := by
  induction n with
  | zero       => rfl
  | succ n' ih => rw [sub_succ, pred_zero, ih]

theorem pred_sub (m n : Nat) : sub (pred m) n = pred (sub m n) := by
  induction m with
  | zero       => rw [pred_zero, zero_sub, pred_zero]
  | succ m' ih => sorry

theorem succ_sub (m n : Nat) : sub (succ m) n = succ (sub m n) := by
  induction n with
  | zero       => rfl
  | succ n' ih => sorry

theorem add_sub (m n : Nat) : sub (add m n) n = m := by
  induction n with
  | zero       => rfl
  | succ n' ih => sorry


example : exp1 zero zero = one := rfl

theorem exp_succ (m n : Nat) : exp1 m (succ n) = mul (succ m) (exp1 m n) := rfl

theorem one_exp (n : Nat) : exp1 zero n = one := by
  induction n with
  | zero       => rfl
  | succ n' ih => rw [exp_succ, ih, mul_one, one]

example : exp1 one one = two := rfl

example : exp1 zero two = one := rfl

example : exp1 one three = eight := rfl

theorem exp_one (n : Nat) : exp1 n one = succ n := by
  induction n with
  | zero       => rfl
  | succ n' ih => rfl

theorem exp_zero (n : Nat) : exp1 n zero = one := by
  match n with
  | zero    => rfl
  | succ n' => rfl

theorem exp_dist (k n m : Nat) : mul (exp1 k m) (exp1 k n) = exp1 k (add m n) := sorry
