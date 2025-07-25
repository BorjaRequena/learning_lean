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
  rw [exp_le_exp]  -- The ↔ rewrites the goal to an equivalent one a ≤ b
  exact h

/- In bi-implications of the form `h : A ↔ B`, we can take the forward, A → B, and reverse, A ← B,
directions with `h.mp` and `h.mpr`, respectively. Here, mp stands for “modus ponens” and mpr stands
for “modus ponens reverse.” You can also use `h.1` and `h.2` for `h.mp` and `h.mpr`, respectively,
if you prefer. Thus the following proof works:
-/

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le  -- Create 2 goals: a + exp c < b + exp d and exp e ≤ exp e
  -- Use dot notation to prove the first goal
  · apply add_lt_add_of_le_of_lt h₀  -- Change goal to prove exp c < exp d given that a ≤ b
    apply exp_lt_exp.mpr h₁  -- Use reverse of exp x < exp y ↔ x < y to prove exp c < exp d given c < d
  apply le_refl -- Prove the second goal exp e ≤ exp e

-- EXERCISE: prove the following theorems using the first one as example to solve numerical goals
example : (0 : ℝ) < 1 := by norm_num

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  -- apply exp_le_exp.mpr  -- This line does the same as the previous one
  apply add_le_add_left h₀  -- Dunno why I couldn't use exact

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  -- Alternative proof using linarith
  have : exp (a + d) ≤ exp (a + e) := by
    rw [exp_le_exp]
    linarith
  linarith [this]

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    apply add_pos  -- Creates 2 goals: 0 < 1 and 0 < exp a
    · norm_num  -- Prove 0 < 1
    · apply exp_pos  -- Prove 0 < exp a

  apply log_le_log h₀  -- Remove the logs for both arguments being always positive
  apply add_le_add  -- Creates 2 goals: 1 ≤ 1 and exp a ≤ exp b
  · norm_num  -- Prove 1 ≤ 1. Could also be done with `le_refl`
  exact exp_le_exp.mpr h  -- Prove exp a ≤ exp b given that a ≤ b

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  -- Alternative proof using linarith
  have h₀ : 0 < 1 + exp a := by
    linarith [exp_pos a]
  apply log_le_log h₀
  apply add_le_add_left (exp_le_exp.mpr h)  -- More compact syntax

/- It is clear that finding the right tactics we need to carry out the proofs is a great part of
writing them. There are multiple sources like:
- Mathlib's repo: https://github.com/leanprover-community/mathlib4
- Mathlib's docs: https://leanprover-community.github.io/mathlib4_docs/
- Loogle: https://loogle.lean-lang.org
- LeanExplore: https://www.leanexplore.com
...

One way is to use the `apply?` tactic, which tries to find the relevant theorem in the library.
-/

example : 0 ≤ a ^ 2 := by
  apply?  -- Try this: exact sq_nonneg a

-- EXERCISE: prove the following theorem using `apply?`
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply?  -- Finds a full strategy to prove the goal


-- Here's another example of an inequality
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) := add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring

/- In this example, we find a few things worth highlighting. First, an expression s ≥ t is
definitionally equivalent to t ≤ s. In principle, this means one should be able to use them
interchangeably. But some of Lean’s automation does not recognize the equivalence, so Mathlib tends
to favor ≤ over ≥. Second, we have used the ring tactic extensively. It is a real timesaver!
Finally, notice that in the second line of the second calc proof, instead of writing by
`exact add_le_add (le_refl _) h`, we can simply write the proof term `add_le_add (le_refl _) h`.

In fact, the only cleverness in the proof above is figuring out the hypothesis h. Once we have it,
the second calculation involves only linear arithmetic, and linarith can handle it.
-/

example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
  linarith

-- EXERCISE: Use these ideas to prove the following theorem. You can use the theorem `abs_le'.mpr`.
-- You will also need the constructor tactic to split a conjunction to two goals. Learn more about
-- it in https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#conjunction-and-biimplication
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  have h₀ : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h₀' : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
      calc
        a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith
  have h₁ : -(a * b) ≤ (a ^ 2 + b ^ 2) / 2 := by
    have h₁' : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2 := by
      calc
        a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
    linarith
  apply abs_le'.mpr  -- The new goal is a conjunction of propositions A ∧ B
  constructor  -- Splits the goal into two goals: A and B
  · exact h₀
  · exact h₁

#check abs_le'.mpr
