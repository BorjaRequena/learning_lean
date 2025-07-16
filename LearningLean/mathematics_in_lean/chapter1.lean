import Mathlib

-- Eval will evaluate the expression and print the result.
#eval "Hello, world!"

-- Check will print the type of the expression.
#check 2 + 2

def f (x : Nat) := x + 3
#check f

-- Some expressions have type Prop. These are mathematical statements.
def FermatLastTheoremAgain := ∀ (x y z n : Nat), n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheoremAgain

-- Some expressions have type P, where P has type Prop. This is a proof of P.
theorem easy_theorem : 2 + 2 = 4 := rfl

#check easy_theorem

theorem hard_theorem : FermatLastTheoremAgain := by
  sorry

#check hard_theorem

-- We can use tactics to prove theorems. For example, let's prove that if n is even, n * m is also even.

-- These first 2 cases break due to type mismatches:
-- example : ∀ m n : ℕ, Even n → Even (n * m) :=
--   fun m n (k, hk) ↦ (m * k, by rw [hk, mul_add])

-- example : ∀ m n : Nat, Even n → Even (n * m) := by
--   rintro m n (k, hk)
--   use m * k
--   rw [hk]
--   ring

-- These work:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩
  use m * k
  rw [hk]
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros
  simp [*, parity_simps]
