import Mathlib

-- Lean provides the rw tactic to replace the left-hand side of an identity by the right-hand side
-- of the goal. If a, b, and c are real numbers, mul_assoc a b c is the identity
-- a * b * c = a * (b * c) and mul_comm a b is the identity a * b = b * a.Lean provides automatiion
-- that generally eliminates the need to refer the facts like these explicitly.
-- Multiplication associates to the left, so the left-hand side of mul_assoc could also be written
-- (a * b) * c. However, it is generally good style to be mindful of Lean’s notational conventions
-- and leave out parentheses when Lean does as well.

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Exercises:
example (a b c : ℝ) : c * b * a = b * (c * a) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
-- To remove the parentheses, we can use the ← (\left) symbol to apply the mul_assoc in reverse.
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

-- Now that we know how to use rw and mul_assoc and mul_comm, we can start doing more complex stuff
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  sorry
