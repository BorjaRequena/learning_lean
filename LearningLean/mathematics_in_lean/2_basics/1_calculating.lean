import Mathlib

/-
2.1 ** Calculating **
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#calculating

Lean provides the rw tactic to replace the left-hand side of an identity by the right-hand side
of the goal. If a, b, and c are real numbers, `mul_assoc a b c` is the identity
`a * b * c = a * (b * c)` and `mul_comm a b` is the identity `a * b = b * a`. Lean provides
automation that generally eliminates the need to refer the facts like these explicitly.

Multiplication associates to the left, so the left-hand side of `mul_assoc` could also be written
`(a * b) * c`. However, it is generally good style to be mindful of Lean’s notational conventions
and leave out parentheses when Lean does as well.
-/

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- EXERCISE:
example (a b c : ℝ) : c * b * a = b * (c * a) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]

-- EXERCISE:
example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
-- To remove the parentheses, we can use the ← (\left) symbol to apply the mul_assoc in reverse.
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- Now that we know how to use rw and mul_assoc and mul_comm, we can start doing more complex stuff
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

-- We can take the same example and write the multiple rewrites in a single line.
-- EXERCISE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]  -- We can see the progress after each comma

-- We can declare variables once and for all outside an example or theorem.
-- EXERCISE:
variable (a b c d e f : ℝ)
example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

-- We can delimit the scope of variable declaration using `section` and `end`.
section
variable (a b c : ℝ)
#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
end

-- Let's see some more examples. The `two_mul` theorem states that `2 * a = a + a`, the theorem
-- `add_mul` states that `(a + b) * c = a * c + b * c`, `mul_add` states that
-- `a * (b + c) = a * b + a * c`, `add_assoc` states that `a + (b + c) = (a + b) + c`.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- Despite this being simple algebraic manipulation, it is hard to understand what is going on at
-- every step. We can use the `calc` keyword to write the proof line by line. Notice that `calc` is
-- a proof term itself, so the proof does not begin with `by`.
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- A common way to write a proof is to use a `calc` with an outline of the main steps. If Lean
-- accepts it, then we can start trying to justify them individually. For example:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry

-- Now let's try proving the following theorem using both pure `rw` and `calc`.
-- EXERCISE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry

  -- With `calc`
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = (a + b) * c + (a + b) * d := by
      rw [mul_add]
    _ = a * c + b * c + a * d + b * d := by
      rw [add_mul, add_mul, ← add_assoc]
    _ = a * c + a * d + b * c + b * d := by
      rw [add_assoc (a * c), add_comm (b * c), ← add_assoc]

  -- With `rw` only
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul, ← add_assoc]
  rw [add_assoc (a * c), add_comm (b * c), ← add_assoc]

-- EXERCISE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  calc
    (a + b) * (a - b) = a * a + b * a - a * b - b * b := by
      rw [mul_sub, add_mul, add_mul, ← sub_sub]
    _ = a * a - b * b := by
      -- I am not sure I can use `add_tsub_cancel_right`, but how can I cancel two terms otherwise?
      rw [mul_comm b a, add_tsub_cancel_right (a * a) (a * b)]
    _ = a ^ 2 - b ^ 2 := by
      rw [pow_two a, pow_two b]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check sub_add_cancel a b
#check add_tsub_cancel_right (a*a) (a*b)

-- We can also rewrite an assumption in the context
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp  -- Replace b with a * d in hyp
  rw [mul_comm d a] at hyp  -- Replace d * a by a * d in hyp
  rw [← two_mul (a * d)] at hyp  -- Replace a * d + a * d by 2 * (a * d) in hyp
  rw [← mul_assoc 2 a d] at hyp  -- Replace 2 * (a * d) by 2 * a * d in hyp
  exact hyp  -- Hyp matches the goal exactly

-- Mathlib offers the RING TACTIC, which is designed to prove identities in any commutative ring as
-- long as they follow from the ring axioms.
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- There is a variation of `rw` called `nth_rw` that allows to replace only particular instances of
-- an expression in the goal. Matches are enumerated strating from 1
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]  -- Replace the second occurrence of `a + b` by `c`
  rw [add_mul]
