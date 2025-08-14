import Mathlib

/-
** Disjunction **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#disjunction

You have already seen that the conjunction symbol, `∧`, is used to express “and.” The `constructor`
tactic allows you to prove a statement of the form `A ∧ B` by proving `A` and then proving `B`.
-/

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

/- We cannot use an anonymous constructor to construct a proof of an “or” because Lean would have
to guess which disjunct we are trying to prove. When we write proof terms we can use `Or.inl` and
`Or.inr` instead to make the choice explicitly. Here, `inl` is short for “introduction left” and
`inr` is short for “introduction right.”
-/

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

/- It may seem strange to prove a disjunction by proving one side or the other. In practice, which
case holds usually depends on a case distinction that is implicit or explicit in the assumptions
and the data. The `rcases` tactic allows us to make use of a hypothesis of the form `A ∨ B`. In
contrast to the use of `rcases` with conjunction or an existential quantifier, here the `rcases`
tactic produces two goals. Both have the same conclusion, but in the first case, `A` is assumed to
be true, and in the second case, `B` is assumed to be true. In other words, as the name suggests,
the `rcases` tactic carries out a proof by cases. As usual, we can tell Lean what names to use for
the hypotheses. In the next example, we tell Lean to use the name `h` on each branch.
-/

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

/- Notice that the pattern changes from `⟨h₀, h₁⟩` in the case of a conjunction to `h₀ | h₁` in the
case of a disjunction. Think of the first pattern as matching against data the contains *both* an
`h₀` and a `h₁`, whereas second pattern, with the bar, matches against data that contains *either*
an `h₀` or `h₁`. In this case, because the two goals are separate, we have chosen to use the same
name, `h`, in each case.

The absolute value function is defined in such a way that we can immediately prove that `x ≥ 0`
implies `|x| = x` (this is the theorem `abs_of_nonneg`) and `x < 0` implies `|x| = -x` (this is
`abs_of_neg`). The expression `le_or_gt 0 x` establishes `0 ≤ x ∨ x < 0`, allowing us to split on
those two cases.

Lean also supports the computer scientists’ pattern-matching syntax for disjunction. Now the cases
tactic is more attractive, because it allows us to name each `case`, and name the hypothesis that
is introduced closer to where it is used.
-/

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

/- The names `inl` and `inr` are short for “intro left” and “intro right,” respectively. Using
`case` has the advantage that you can prove the cases in either order; Lean uses the tag to find
the relevant goal. If you don’t care about that, you can use `next`, or `match`, or even a pattern-
matching `have`.
-/

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

/- In the case of `match`, we need to use the full names `Or.inl` and `Or.inr` of the canonical
ways to prove a disjunction. In this textbook, we will generally use `rcases` to split on the cases
of a disjunction.

Try proving the triangle inequality using the first two theorems in the next snippet. They are
given the same names they have in Mathlib.
-/

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
