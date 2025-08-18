import Mathlib

/-
** Disjunction **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#disjunction

The canonical way to prove a disjunction `A ∨ B` is to prove `A` or to prove `B`. The left tactic
chooses `A`, and the right tactic chooses `B`.
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
-/

--EXERCISE: prove the following theorems to prove the triangle inequality.
namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · -- with h : 0 ≤ x + y
    rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · -- with h : 0 > x + y
    rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

-- EXERCISE: if you've enjoyed these, prove the following ones as well

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]  -- With h : 0 ≤ y
    constructor
    · show x < y → x < y ∨ x < -y
      intro h'
      left
      exact h'
    · show x < y ∨ x < -y → x < y
      intro h'  -- Introduce hypothesis h' : x < y ∨ x < -y
      rcases h' with h' | h'
      · exact h'  -- Prove x < y with h' : x < y
      · linarith  -- Prove x < y with h' : x < -y
  · rw [abs_of_neg h]  -- With h: 0 > y
    constructor
    · show x < -y → x < y ∨ x < -y
      intro h'
      right
      exact h'
    · show x < y ∨ x < -y → x < -y
      intro h'
      rcases h' with h' | h'
      · linarith  -- Prove x < -y with h' : x < y
      · exact h'  -- Prove x < -y with h' : x < -y

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]  -- With h : 0 ≤ x
    constructor
    · show x < y → -y < x ∧ x < y
      intro h'  -- Introduce hypothesis x < y
      constructor
      · show -y < x
        linarith
      · show x < y
        exact h'
    · show -y < x ∧ x < y → x < y
      intro h'  -- Introduce hypothesis -y < x ∧ x < y
      rcases h' with ⟨h₁, h₂⟩  -- Split h' into h₁ : -y < x and h₂ : x < y
      exact h₂
  · rw [abs_of_neg h]  -- With h: 0 > x
    constructor
    · show -x < y → -y < x ∧ x < y
      intro h'
      constructor
      · show -y < x
        linarith
      · show x < y
        linarith
    · show -y < x ∧ x < y → -x < y
      intro h'
      linarith

end MyAbs

/- You can also use `rcases` and `rintro` with nested disjunctions. When these result in a genuine
case split with multiple goals, the patterns for each new goal are separated by a vertical bar.
-/

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

/- You can still nest patterns and use the `rfl` keyword to substitute equations:
-/

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

-- EXERCISE: prove the following with a single line.
-- Hint: Use rcases to unpack the hypotheses combined with semicolon and linarith.

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [pow_two_nonneg x, pow_two_nonneg y]

/- On the real numbers, an equation `x * y = 0` tells us that `x = 0` or `y = 0`. In Mathlib, this
fact is known as `eq_zero_or_eq_zero_of_mul_eq_zero`, and it is another nice example of how a
disjunction can arise.
-/

-- EXERCISE: use `eq_zero_or_eq_zero_of_mul_eq_zero` to prove the following theorem.
-- Hint: Use the `ring` tactic to help with calculations.

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · show x = 1 ∨ x = -1  -- With h1 : x + 1 = 0
    right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · show x = 1 ∨ x = -1  -- With h1 : x - 1 = 0
    left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · show x = y ∨ x = -y  -- With h1 : x + y = 0
    right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · show x = y ∨ x = -y  -- With h1 : x - y = 0
    left
    exact eq_of_sub_eq_zero h1

/- In an arbitrary ring R, an element `x` such that `x * y = 0` for some nonzero `y` is called a
*left zero divisor*, an element `x` such that `y * x = 0` for some nonzero `y` is called a
*right zero divisor*, and an element that is either a left or right zero divisor is called simply a
*zero divisor*. The theorem `eq_zero_or_eq_zero_of_mul_eq_zero` says that the real numbers have no
nontrivial zero divisors. A commutative ring with this property is called an integral domain. Your
proofs of the two theorems above should work equally well in any integral domain:
-/
section

variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  -- Copy the code from above
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · show x = 1 ∨ x = -1  -- With h1 : x + 1 = 0
    right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · show x = 1 ∨ x = -1  -- With h1 : x - 1 = 0
    left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  -- Copy the code from above
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · show x = y ∨ x = -y  -- With h1 : x + y = 0
    right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · show x = y ∨ x = -y  -- With h1 : x - y = 0
    left
    exact eq_of_sub_eq_zero h1

/- In fact, if you are careful, you can prove the first theorem without using commutativity of
multiplication. In that case, it suffices to assume that `R` is a `Ring` instead of a `CommRing`.

Sometimes in a proof we want to split on cases depending on whether some statement is true or not.
For any proposition `P`, we can use `em P : P ∨ ¬ P`. The name `em` is short for “excluded middle.”
-/

example (P : Prop) : ¬¬P → P := by
  intro h  -- Introduce hypothesis h : ¬¬P
  cases em P
  · assumption  -- Prove P with h' : P
  · contradiction  -- Prove P with h' : ¬P

/- Alternatively, you can use the `by_cases` tactic.
-/

example (P : Prop) : ¬¬P → P := by
  intro h  -- Introduce hypothesis h : ¬¬P
  by_cases h' : P
  · assumption  -- Prove P with h' : P
  · contradiction  -- Prove P with h' : ¬P

/- Notice that the `by_cases` tactic lets you specify a label for the hypothesis that is introduced
in each branch, in this case, `h' : P` in one and `h' : ¬ P` in the other. If you leave out the
label, Lean uses `h` by default.
-/

-- EXERCISE: prove the following equivalence using `by_cases` to establish one direction.

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · show (P → Q) → ¬P ∨ Q
    intro h  -- Introduce hypothesis h : P → Q
    by_cases h' : P
    · show ¬P ∨ Q  -- With h' : P
      right
      exact h h'
    · show ¬P ∨ Q  -- With h' : ¬P
      left
      exact h'
  · show ¬P ∨ Q → P → Q
    rintro (h | h)
    · show P → Q  -- With h : ¬P
      intro h'  -- h' : P directly contradcits h : ¬P
      -- contradiction
      exact absurd h' h
    · show P → Q  -- With h : Q
      intro  -- Take P for granted
      exact h  -- Solve directly with h : Q
