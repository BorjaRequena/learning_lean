import Mathlib

/-
** 2.3 Using Theorems and Lemmas **
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#using-theorems-and-lemmas

Rewriting is great for proving equations, but that does not cover other sorts of theorems. For
example, how can we prove a + eᵇ ≤ a + eᶜ holds whenever b ≤ c? We have seen that theorems can be
applied to arguments and hypotheses, and that the `apply` and `exact` tactics can be used to solve
goals. In this section, we will make good use of these tools.
-/

variable (a b c d e : ℝ)
open Real  -- for exp_le_exp and other theorems for reals

-- Consider the theorems `le_refl` and `le_trans`:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

/- the implicit parentheses in the statement of le_trans associate to the right, so it should be
interpreted as a ≤ b → (b ≤ c → a ≤ c). The library designers have set the arguments a, b and c to
`le_trans` implicit, so that Lean will not let you provide them explicitly (unless you really
insist, as we will discuss later). Rather, it expects to infer them from the context in which they
are used. For example, when hypotheses `h : a ≤ b` and `h' : b ≤ c` are in the context, all the
following work:
-/
section
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)

end

/- The `apply` tactic takes a proof of a general statement or implication, tries to match the
conclusion with the current goal, and leaves the hypotheses, if any, as new goals. If the given
proof matches the goal exactly (modulo definitional equality), you can use the `exact` tactic
instead of `apply`.
-/

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans  -- Creates two goals: x ≤ y and y ≤ z
  -- Now we need to prove both new goals. We can indicate that with dots (although optional)
  · apply h₀  -- Solves the first goal
  · apply h₁  -- Solves the second goal

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀  -- Replaces the goal with another one
  apply h₁  -- Proves the new goal

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁  -- Proves the goal directly

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x

-- We have a few more library theorems similar to these
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

-- EXERCISE: prove the following theorem using `exact` and `apply`
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_trans  -- We say a < z < e. This gives two goals: prove that a < z and z < e (z tbd)
  apply lt_of_le_of_lt h₀ h₁  -- Proves that a < c (c replaces placeholder z), new goal is c < e
  exact lt_of_le_of_lt h₂ h₃  -- Proves that c < e, we're done

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt h₀  -- Proves a ≤ b, new goal is to prove b < e
  apply lt_trans h₁  -- Proves b < e, new goal is to prove c < e
  exact lt_of_le_of_lt h₂ h₃  -- Proves c < e, we're done

-- Lean has a `linarith` tactic designed to handle linear arithmetic that can do this proof
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

/- In addition to equations and inequalities in the context, we can provide `linarith` with
additional inequalities passing them as arguments. For instance, we can provide `linarith` with a
partial proof of the theorem.
-/

example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']  -- exp_le_exp.mpr h' is the proof of exp b ≤ exp c

-- There are plenty of theorems that can be used to establish inequalities on the real numbers
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

-- Some theorems use *bi-implication* (↔) "if and only if". These can be used with `rw`
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]  -- The ↔ rewrites the goal to a new one a ≤ b
  exact h
