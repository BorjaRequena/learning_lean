import Mathlib

/-
** 3.2 The existential quantifier **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#the-existential-quantifier

The existential quantifier, which can be entered as \ex in VS Code, is used to represent the phrase
“there exists.” The formal expression `∃ x : ℝ, 2 < x ∧ x < 3` in Lean says that there is a real
number between 2 and 3. (We will discuss the conjunction symbol, ∧, in Section 3.4.) The canonical
way to prove such a statement is to exhibit a real number and show that it has the stated property.
The number 2.5, which we can enter as `5 / 2` or `(5 : ℝ) / 2` when Lean cannot infer from context
that we have the real numbers in mind, has the required property, and the `norm_num` tactic can
prove that it meets the description.

There are a few ways we can put the information together. Given a goal that begins with an
existential quantifier, the `use` tactic is used to provide the object, leaving the goal of proving
the property.
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

-- You can give the `use` tactic proofs as well as data

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2

-- In fact, the `use` tactic automatically tries to use the available assumptions

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2

-- We can use *anonymous constructor* notation to construct a proof of an existential quantifier.

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

/- Notice that there is no `by`; here we are giving an explicit proof term. The left and right
angle brackets, which can be entered as `\<` and `\>` respectively, tell Lean to put together the
given data using whatever construction is appropriate for the current goal. We can use the notation
without going first into tactic mode:
-/

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

/- So now we know how to *prove* an exists statement. But how do we *use one*? If we know that there
exists an object with a certain property, we should be able to give a name to an arbitrary one and
reason about it. For example, remember the predicates `FnUb f a` and `FnLb f a` from the last
section 3.1, which say that `a` is an upper bound or lower bound on `f`, respectively. We can use
the existential quantifier to say that “`f` is bounded” without specifying the bound:
-/

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

/- We can use the theorem `FnUb_add` from section 3.1 to prove that if `f` and `g` have upper
bounds, then so does `fun x ↦ f x + g x`.
-/

-- Restating the `fnUb_add` theorem from section 3.1
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section
variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb

/- The `rcases` tactic unpacks the information in the existential quantifier. The annotations like
`⟨a, ubfa⟩`, written with the same angle brackets as the anonymous constructors, are known as
*patterns*, and they describe the information that we expect to find when we unpack the main
argument. Given the hypothesis `ubf` that there is an upper bound for
`f`, `rcases ubf with ⟨a, ubfa⟩` adds a new variable `a` for an upper bound to the context,
together with the hypothesis `ubfa` that it has the given property. The goal is left unchanged;
what *has* changed is that we can now use the new object and the new hypothesis to prove the goal.
This is a common method of reasoning in mathematics: we unpack objects whose existence is asserted
or implied by some hypothesis, and then use it to establish the existence of something else.

Try using this method to establish the following. You might find it useful to turn some of the
examples from the last section into named theorems, as we did with `fn_ub_add`, or you can insert
the arguments directly into the proofs.
-/

-- EXERCISE: prove the following couple of theorems
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

/- The “r” in `rcases` stands for “recursive,” because it allows us to use arbitrarily complex
patterns to unpack nested data. The `rintro` tactic is a combination of `intro` and `rcases`:
-/

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- In fact, Lean also supports a pattern-matching fun in expressions and proof terms:

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

end

/- Think of the first `obtain` instruction as matching the “contents” of `ubf` with the given
pattern and assigning the components to the named variables. `rcases` and `obtain` are said to
destruct their arguments.

Lean also supports syntax that is similar to that used in other functional programming languages:
-/

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩

/- In the first example, if you put your cursor after cases `ubf`, you will see that the tactic
produces a single goal, which Lean has tagged `intro`. (The particular name chosen comes from the
internal name for the axiomatic primitive that builds a proof of an existential statement.) The
`case` tactic then names the components. The second example is similar, except using `next` instead
of `case` means that you can avoid mentioning `intro`. The word `match` in the last two examples
highlights that what we are doing here is what computer scientists call “pattern matching.” Notice
that the third proof begins by `by`, after which the tactic version of `match` expects a tactic
proof on the right side of the arrow. The last example is a proof term: there are no tactics in
sight.

For the rest of this book, we will stick to `rcases`, `rintro`, and `obtain`, as the preferred
ways of using an existential quantifier. But it can’t hurt to see the alternative syntax,
especially if there is a chance you will find yourself in the company of computer scientists.

To illustrate one way that `rcases` can be used, we prove an old mathematical chestnut: if two
integers `x` and `y` can each be written as a sum of two squares, then so can their product,
`x * y`. In fact, the statement is true for any commutative ring, not just the integers. In the
next example, `rcases` unpacks two existential quantifiers at once. We then provide the magic
values needed to express `x * y` as a sum of squares as a list to the `use` statement, and we use
`ring` to verify that they work.
-/

section

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d , a * d + b * c  -- For the ∃ a b in SumOfSquares use these values
  ring

/- This proof doesn’t provide much insight, but here is one way to motivate it. A Gaussian integer
is a number of the form `a + bi` where `a` and `b` are integers and `i = sqrt{-1}`. The norm of the
Gaussian integer `a + bi` is defined by `a^2 + b^2`. So the norm of a Gaussian integer is a
sum of squares, and any sum of squares can be expressed in this way. The theorem above reflects
the fact that norm of a product of Gaussian integers is the product of their norms: if `a` is the
norm of `x` and `b` is the norm of `y` in the norm of `x * y`, then `a * b` is the norm of `x * y`.
Our cryptic proof illustrates the fact that the proof that is easiest to formalize isn’t always the
most perspicuous one. In Section 7.3, we will provide you with the means to define the Gaussian
integers and use them to provide an alternative proof.

The pattern of unpacking an equation inside an existential quantifier and then using it to rewrite
an expression in the goal comes up often, so much so that the `rcases` tactic provides an
abbreviation: if you use the keyword `rfl` in place of a new identifier, `rcases` does the
rewriting automatically (this trick doesn’t work with pattern-matching lambdas).
-/

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩  -- `rfl` automatically rewrites `x = a ^ 2 + b ^ 2`
  rcases sosy with ⟨c, d, rfl⟩  -- `rfl` automatically rewrites `y = c ^ 2 + d ^ 2`
  -- No rw needed here, this is a more compact proof
  use a * c - b * d, a * d + b * c
  ring

end

/- As with the universal quantifier, you can find existential quantifiers hidden all over if you
know how to spot them. For example, divisibility is implicitly an “exists” statement.
-/

section
variable (a b c : ℕ)

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e
  ring

/- And once again, this provides a nice setting for using `rcases` with `rfl`. Try it out in the
proof above. It feels pretty good!
-/

-- EXERCISE: Try using `rcases` with `rfl` in the previous proof
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e
  ring

-- EXERCISE: Try proving the following
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e
  ring

end

/- For another important example, a function `f : α ↦ β` is said to be *surjective* if for every
`y` in the codomain, `β`, there is an `x` in the domain, `α`, such that `f(x) = y`. Notice that
this statement includes both a universal and an existential quantifier, which explains why the next
example makes use of both `intro` and `use`.
-/
-- It's something like: ∀ y ∈ β, ∃ x ∈ α s.t. f x = y

section
open Function  -- Need to open the Function namespace to use the Surjective predicate

example {c : ℝ} : Surjective fun x ↦ x + c := by
  -- The goal is actually ∀ (b : ℝ), ∃ a, a + c = b (see with `dsimp [Surjective]`)
  intro x  -- Break the ∀ (b : ℝ)
  use x - c  -- Give a the value x - c to undo the ∃ a
  dsimp  -- Simplify the goal: x - c + c = x
  ring  -- Piece of cake!

/- At this point, it is worth mentioning that there is a tactic, `field_simp`, that will often
clear denominators in a useful way. It can be used in conjunction with the `ring` tactic.
-/

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]  -- Clear denominator, the new goal is x ^ 2 - y ^ 2 = (x + y) * (x - y)
  ring

/- The next example uses a surjectivity hypothesis by applying it to a suitable value. Note that
you can use `rcases` with any expression, not just a hypothesis.
-/

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩  -- Apply the surjectivity to a constant function -> f x = 2
  use x  -- We have a value x s.t. f x = 2
  rw [hx]  -- Replace f x ^ 2 = 2 with 2 ^ 2 = 4
  norm_num

end

-- EXERCISE: use these methods to show that the composition of surjective functions is surjective
section

open Function

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  dsimp [Surjective]  -- The goal is ∀ (b : γ), ∃ a, g (f a) = b
  intro y  -- ∃ a, g (f a) = y
  rcases surjg y with ⟨x, rfl⟩  -- ∃ a, g (f a) = g x
  rcases surjf x with ⟨z, rfl⟩  -- ∃ a, g (f a) = g (f z)
  use z  -- Choose z as the value we take for a, proving the goal

end
