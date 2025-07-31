import Mathlib

/-
** 3.3 Negation **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#negation

The symbol `¬` is meant to express negation, so `¬ x < y` says that `x` is not less than `y`,
`¬ x = y` (or, equivalently, `x ≠ y`) says that `x` is not equal to `y`, and `¬ ∃ z, x < z ∧ z < y`
says that there does not exist a `z` strictly between `x` and `y`. In Lean, the notation `¬ A`
abbreviates `A → False`, which you can think of as saying that `A` implies a contradiction.
Practically speaking, this means that you already know something about how to work with negations:
you can prove `¬ A` by introducing a hypothesis `h : A` and proving `False`, and if you have
`h : ¬ A` and `h' : A`, then applying `h` to `h'` yields `False`.

To illustrate, consider the irreflexivity principle `lt_irrefl` for a strict order, which says that
we have `¬ a < a` for every `a`. The asymmetry principle `lt_asymm` says that we have
`a < b → ¬ b < a`. Let’s show that `lt_asymm` follows from `lt_irrefl`.
-/

section

variable (a b : ℝ)

#check lt_irrefl
#check lt_asymm

example (h : a < b) : ¬b < a := by
  intro h'  -- Take h : b < a and produce a new goal `False`
  have : a < a := lt_trans h h'
  apply lt_irrefl a this  -- `this` refers to the previous `have` statement

/- This example introduces a couple of new tricks. First, when you use `have` without providing a
label, Lean uses the name `this`, providing a convenient way to refer back to it. Because the proof
is so short, we provide an explicit proof term. But what you should really be paying attention to
in this proof is the result of the intro tactic, which leaves a goal of `False`, and the fact that
we eventually prove `False` by applying `lt_irrefl` to a proof of `a < a`.

Here is another example, which uses the predicate `FnHasUb` defined in section 3.2, which says that
a function has an upper bound.
-/

-- Rewrite the theorems from fections 3.1 and 3.2 to use them here
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

-- Now comes the actual example
variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnhasub  -- Assume f has an upper bound and prove `False`
  rcases fnhasub with ⟨a, fnuba⟩  -- Unpack the previous assumption setting a as upper bound for f
  rcases h a with ⟨x, hx⟩  -- Use the hypothesis to find an x such that f x > a
  have : f x ≤ a := fnuba x  -- Use the upper bound assumption to show that f x ≤ a
  linarith  -- We've reached a contradiction since hx : f x > a and this : f x ≤ a

/- Remember that it is often convenient to use `linarith` when a goal follows from linear equations
and inequalities that are in the context.
-/


-- EXERCISE: prove the following theorems in a similar way
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnhaslb  -- Assume f has a lower bound and prove `False`
  rcases fnhaslb with ⟨a, fnlab⟩  -- Unpack the previous assumption setting a as lower bound for f
  rcases h a with ⟨x, hx⟩  -- Use the hypothesis to find an x such that f x < a
  have : a ≤ f x := fnlab x
  linarith

  -- Repeating the proof with a more compact syntax
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, fnlba⟩  -- Assume a as lower bound for f and prove `False`
  rcases h a with ⟨x, hx⟩  -- Use the hypothesis to find an x such that f x < a
  have := fnlba x  -- Proof object for a ≤ f x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  intro ⟨a, fnuba⟩  -- Assume a as upper bound for f and prove `False`
  have : a + 1 ≤ a := fnuba (a + 1)  -- Use the upper bound assumption to show that a + 1 ≤ a
  linarith  -- We've reached a contradiction since a + 1 ≤ a and this : a + 1 ≤ a

/- Mathlib offers a number of useful theorems for relating orders and negations:
-/

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

/- Recall the predicate `Monotone f`, which says that `f` is nondecreasing.
-/

-- EXERCISE: Use some of the theorems just enumerated to prove the following:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply h at h''
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply h'' at h
  linarith

/- We can show that the first example in the last exercise cannot be proved if we replace < by ≤.
Notice that we can prove the negation of a universally quantified statement by giving a
counterexample.
-/

#check Monotone

-- EXERCISE: complete the following proof
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
-- Let's prove this with a counterexample. The key element is the equality in f a ≤ f b. In
-- monotone functions, a ≤ b → f a ≤ f b, but the opposite is not true, in general. You may think
-- of flat areas in the function, in those cases, f a ≤ f b does not imply a ≤ b since
-- f a = f b ∀ a, b in the flat area.
-- Let's introduce a constant function f(x) = 0, which is monotone, and prove that f 1 ≤ f 0
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by -- Initially sorry
    intro a b aleb  -- Introduce a, b ∈ ℝ and a ≤ b as hypothesis and f a ≤ f b as goal
    rfl  -- f a = 0 and f b = 0, so 0 ≤ 0, we can prove by rfl that will do this step
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'  -- Get the contradiction 1 ≤ 0
  linarith

/- This example introduces the `let` tactic, which adds a local definition to the context. If you
put the cursor after the `let` command, in the goal window you will see that the definition
`f : ℝ → ℝ := fun x ↦ 0` has been added to the context. Lean will unfold the definition of `f` when
it has to. In particular, when we prove `f 1 ≤ f 0` with `le_refl`, Lean reduces `f 1` and `f 0` to
`0`.
-/

-- EXERCISE: use `le_of_not_gt` to prove the following:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt  -- Transform x ≤ 0 to ¬ x > 0
  intro h'  -- Assume x > 0 and prove `False`
  -- have h'' : x < x := h _ h'  -- We can provide this directly to linarith
  linarith [h _ h'] -- Get the contradiction x < x

end

/- Implicit in many of the proofs we have just done is the fact that if `P` is any property, saying
that there is nothing with property `P` is the same as saying that everything fails to have
property `P`, and saying that not everything has property `P` is equivalent to saying that
something fails to have property `P`. In other words, all four of the following implications are
valid (but one of them cannot be proved with what we explained so far):
-/

-- EXERCISE: complete the following proofs
section

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px  -- Assume x has property P and prove `False`
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro ⟨x, Px⟩  -- Assume x has property P and prove `False`
  exact h x Px

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  -- Can't be proved with what we have until now, we need new tools (see below)
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  exact h' x

/- The third example is more difficult than the others because it concludes that an object exists
from the fact that its nonexistence is contradictory. This is an instance of classical mathematical
reasoning. We can use proof by contradiction to prove the third implication as follows
-/

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'  -- Assume ¬∃ x, ¬P x and prove `False`
  apply h  -- The new goal is to show that ∀ x, P x
  intro x  -- The goal is P x
  by_contra h''  -- Assume ¬P x and prove `False`
  exact h' ⟨x, h''⟩  -- We've reached a contradiction since h' : ¬∃ x, ¬P x and this : ∃ x, ¬P x

/- Make sure you understand how this works. The `by_contra` tactic allows us to prove a goal `Q` by
assuming `¬ Q` and deriving a contradiction. In fact, it is equivalent to using the equivalence
`not_not : ¬ ¬ Q ↔ Q`.
-/

-- EXERCISE: prove the forward direction of this equivalence using `by_contra`
-- (the reverse direction follows from the ordinary rules for negation.)
example (h : ¬¬Q) : Q := by
  by_contra h'  -- Assume ¬Q and prove `False`
  exact h h'  -- We've reached a contradiction since h : ¬¬Q and h' : ¬Q

example (h : Q) : ¬¬Q := by
  intro h'  -- Assume ¬¬Q and prove `False`
  exact h' h  -- We've reached a contradiction since h : Q and h' : ¬Q

end

-- EXERCISE: Use proof by contradiction to establish the following:
-- (Hint: use intro first)
section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'  -- Assume ¬∃ x, f x > a and prove `False`
  apply h  -- The new goal is to show that FnHasUb f (hypothesis is the contrary)
  use a  -- Use a for the existence in `FnHasUb` -> `FnUb f a`
  intro x  -- Introudce an x for the ∀ in `FnUb` -> `f x ≤ a`
  apply le_of_not_gt  -- Transform into ¬f x ⋗ a
  by_contra h''  -- Assume it and find a contradiction (could also use intro h'')
  apply h'
  use x

/- It is often tedious to work with compound statements with a negation in front, and it is a
common mathematical pattern to replace such statements with equivalent forms in which the negation
has been pushed inward. To facilitate this, Mathlib offers a `push_neg` tactic, which restates the
goal in this way. The command `push_neg at h` restates the hypothesis `h`.
-/

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

/- In the second example, we use dsimp to expand the definitions of `FnHasUb` and `FnUb`. We need
to use `dsimp` rather than `rw` to expand `FnUb`, because it appears in the scope of a quantifier.
You can verify that in the examples above with `¬∃ x, P x` and `¬∀ x, P x`, the `push_neg` tactic
does the expected thing.
-/

-- EXERCISE: Use `push_neg` to prove the following:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg at h
  exact h


/- Mathlib also has a tactic, `contrapose`, which transforms a goal `A → B` to `¬B → ¬A`.
Similarly, given a goal of proving `B` from hypothesis `h : A`, `contrapose h` leaves you with a
goal of proving `¬A` from hypothesis `¬B`. Using `contrapose!` instead of `contrapose` applies
`push_neg` to the goal and the relevant hypothesis as well.
-/

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

/- We have not yet explained the `constructor` command or the use of the semicolon `<;>` after it,
but we will do that in the next section.

We close this section with the principle of *ex falso*, which says that anything follows from a
contradiction. In Lean, this is represented by `False.elim`, which establishes `False → P` for any
proposition `P`. This may seem like a strange principle, but it comes up fairly often. We often
prove a theorem by splitting on cases, and sometimes we can show that one of the cases is
contradictory. In that case, we need to assert that the contradiction establishes the goal so we
can move on to the next one. (We will see instances of reasoning by cases in Section 3.5.)

Lean provides a number of ways of closing a goal once a contradiction has been reached.
-/
section
variable {a : ℕ}

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

/- The `exfalso` tactic replaces the current goal with the goal of proving `False`. Given `h : P`
and `h' : ¬ P`, the term `absurd h h'` establishes any proposition. Finally, the `contradiction`
tactic tries to close a goal by finding a contradiction in the hypotheses, such as a pair of the
form `h : P` and `h' : ¬ P`. Of course, in this example, `linarith` also works.
-/
