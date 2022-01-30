

def even (n : Nat) : Prop :=
  ∃ m : Nat, n = 2 * m


def prime (n : Nat) : Prop :=
  ¬(
    ∃ p q : Nat,
      (p > 1)
    ∧ (q > 1)
    ∧ (n = p * q)
  )


def infinitely_many_primes : Prop :=
  ∀ n : Nat,
  ∃ p : Nat,
    (p > n)
  ∧ (prime p)


def Fermat_prime (n : Nat) : Prop :=
  ∃ k : Nat,
    (k > 0)
  ∧ (n = 2^k + 1)
  ∧ (prime n)


def infinitely_many_Fermat_primes : Prop :=
  ∀ n : Nat,
  ∃ p : Nat,
    (p > n)
  ∧ (Fermat_prime p)


def goldbach_conjecture : Prop :=
  ∀ n : Nat, (n > 2) ∧ (even n) →
    (
      ∃ p q : Nat,
        (prime p) ∧ (prime q)
      ∧ (p + q = n)
    )

def Goldbach's_weak_conjecture : Prop :=
  ∀ n : Nat, (n > 7) ∧ ¬(even n) →
    (
      ∃ p q r : Nat,
        ¬(even p) ∧ ¬(even q) ∧ ¬(even r)
      ∧ (prime p) ∧ (prime q) ∧ (prime r)
      ∧ (p + q + r = n)
    )


def Fermat's_last_theorem : Prop :=
  ¬(
    ∃ a b c : Nat,
    ∃ n : Nat,
      (a > 0) ∧ (b > 0) ∧ (c > 0)
    ∧ (n > 2)
    ∧ (a^n + b^n = c^n)
  )
