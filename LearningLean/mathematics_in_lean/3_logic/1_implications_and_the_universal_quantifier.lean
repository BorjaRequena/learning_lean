import Mathlib

/-
** 3. Logic **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#

Complex mathematical statements are built up from simple ones like these using logical terms like
“and,” “or,” “not,” and “if … then,” “every,” and “some.” In this chapter, we show you how to work
with statements that are built up in this way.

** 3.1 Implications and the Universal Quantifier **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#implication-and-the-universal-quantifier

Consider the statement after the #check:
-/
#check ∀ x : ℝ, 0 ≤ x → |x| = x

/- In words, we would say “for every real number x, if 0 ≤ x then the absolute value of x equals x”.
We can also have more complicated statements like:
-/
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

/- In words, we would say “for every x, y, and ε, if 0 < ε ≤ 1, the absolute value of x is less
than ε, and the absolute value of y is less than ε, then the absolute value of x * y is less than ε.”
In Lean, in a sequence of implications there are implicit parentheses grouped to the right. So the
expression above means “if 0 < ε then if ε ≤ 1 then if |x| < ε …” As a result, the expression says
that all the assumptions together imply the conclusion.

You have already seen that even though the universal quantifier in this statement ranges over
objects and the implication arrows introduce hypotheses, Lean treats the two in very similar ways.
In particular, if you have proved a theorem of that form, you can apply it to objects and hypotheses
in the same way. We will use as an example the following statement that we will help you to prove
a bit later:
-/

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

/- You have also already seen that it is common in Lean to use curly brackets to make quantified
variables implicit when they can be inferred from subsequent hypotheses. When we do that, we can
just apply a lemma to the hypotheses without mentioning the objects.
-/

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

/- At this stage, you also know that if you use the apply tactic to apply my_lemma to a goal of the
form |a * b| < δ, you are left with new goals that require you to prove each of the hypotheses.

To prove a statement like this, use the intro tactic. Take a look at what it does in this example:
-/

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt  -- Intorduces a series of hypotheses that match the the conditions
  sorry

/- We can use any names we want for the universally quantified variables; they do not have to be x,
y, and ε. Notice that we have to introduce the variables even though they are marked implicit:
making them implicit means that we leave them out when we write an expression using `my_lemma`, but
they are still an essential part of the statement that we are proving. After the `intro` command,
the goal is what it would have been at the start if we listed all the variables and hypotheses
before the colon, as we did in the last section. In a moment, we will see why it is sometimes
necessary to introduce variables and hypotheses after the proof begins.

Finish the proof using the theorems `abs_mul`, `mul_le_mul`, `abs_nonneg`, `mul_lt_mul_right`,
and `one_mul`. Remember that you can find theorems like these using Ctrl-space completion. Remember
also that you can use `.mp` and `.mpr` or `.1` and `.2` to extract the two directions of an `iff`
statement.
-/

-- EXERCISE: prove the following theorem
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by
      apply mul_le_mul
      · show |x| ≤ |x|
        apply le_refl
      · show |y| ≤ ε
        linarith
      · show 0 ≤ |y|
        apply abs_nonneg
      · show 0 ≤ |x|
        apply abs_nonneg
    _ < 1 * ε := by
      rw [mul_lt_mul_right epos]
      linarith
    _ = ε := by exact one_mul ε

/- Universal quantifiers are often hidden in definitions, and Lean will unfold definitions to
expose them when necessary. For example, let’s define two predicates, `FnUb f a` and `FnLb f a`,
where `f` is a function from the real numbers to the real numbers and `a` is a real number. The
first says that `a` is an upper bound on the values of `f`, and the second says that `a` is a lower
bound on the values of `f`.
-/

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ (f x)

/- In the next example, `fun x ↦ f x + g x` is the function that maps x to `f x + g x`. Going from
the expression `f x + g x` to this function is called a lambda abstraction in type theory.
-/

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  -- change f x + g x ≤ a + b  -- Does the same as `dsimp` in this case
  apply add_le_add
  apply hfa
  apply hgb

/- Applying `intro` to the goal `FnUb (fun x ↦ f x + g x) (a + b)` forces Lean to unfold the
definition of `FnUb` and introduce `x` for the universal quantifier. The goal is then
`(fun (x : ℝ) ↦ f x + g x) x ≤ a + b`. But applying `(fun x ↦ f x + g x)` to `x` should result in
`f x + g x`, and the `dsimp` command performs that simplification. (The “d” stands for
“definitional.”) You can delete that command and the proof still works; Lean would have to perform
that contraction anyhow to make sense of the next `apply`. The `dsimp` command simply makes the
goal more readable and helps us figure out what to do next. Another option is to use the `change`
tactic by writing `change f x + g x ≤ a + b`. This helps make the proof more readable, and gives
you more control over how the goal is transformed.

The rest of the proof is routine. The last two `apply` commands force Lean to unfold the definitions
of `FnUb` in the hypotheses.
-/

-- EXERCISE: carry out the following similar proofs
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x  -- Now the goal is a + b ≤ (fun x ↦ f x + g x) x
  dsimp  -- Simplify the goal by definition: a + b ≤ f x + g x
  apply add_le_add
  · show a ≤ f x
    apply hfa
  · show b ≤ g x
    apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp  -- The goal is 0 ≤ f x * g x
  apply mul_nonneg
  · show 0 ≤ f x
    apply nnf
  · show 0 ≤ g x
    apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  dsimp  -- The goal is f x * g x ≤ a * b
  apply mul_le_mul
  · show f x ≤ a
    apply hfa
  · show g x ≤ b
    apply hgb
  · show 0 ≤ g x
    apply nng
  · show 0 ≤ a
    apply nna

/- Even though we have defined `FnUb` and `FnLb` for functions from the reals to the reals, you
should recognize that the definitions and proofs are much more general. The definitions make sense
for functions between any two types for which there is a notion of order on the codomain. Checking
the type of the theorem `add_le_add` shows that it holds of any structure that is an “ordered
additive commutative monoid”; the details of what that means don’t matter now, but it is worth
knowing that the natural numbers, integers, rationals, and real numbers are all instances. So if we
prove the theorem `fnUb_add` at that level of generality, it will apply in all these instances.
-/
section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

#check fnUb_add

end

/- For another example of a hidden universal quantifier, Mathlib defines a predicate `Monotone`,
which says that a function is nondecreasing in its arguments:
-/

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

/- The property `Monotone f` is defined to be exactly the expression after the colon. We need to
put the @ symbol before h because if we don’t, Lean expands the implicit arguments to h and inserts
placeholders.

Proving statements about monotonicity involves using `intro` to introduce two variables, say, a and
b, and the hypothesis a ≤ b. To use a monotonicity hypothesis, you can apply it to suitable
arguments and hypotheses, and then apply the resulting expression to the goal. Or you can apply it
to the goal and let Lean help you work backwards by displaying the remaining hypotheses as new
subgoals.
-/
section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb  -- Introduces a, b ∈ ℝ as variables and a ≤ b as hypothesis
  -- The goal is (fun x ↦ f x + g x) a ≤ (fun x ↦ f x + g x) b
  -- A dsimp would make it f a + g a ≤ f b + g b but the following apply already does it
  apply add_le_add  -- Generates two subgoals: f a ≤ f b and g a ≤ g b
  apply mf aleb  -- Proves f a ≤ f b given the monotonicity of f and a ≤ b
  apply mg aleb  -- Proves g a ≤ g b given the monotonicity of g and a ≤ b

/- When a proof is this short, it is often convenient to give a proof term instead. To describe a
proof that temporarily introduces objects a and b and a hypothesis aleb, Lean uses the notation
`fun a b aleb ↦ ....` This is analogous to the way that an expression like `fun x ↦ x^2` describes
a function by temporarily naming an object, x, and then using it to describe a value. So the
`intro` command in the previous proof corresponds to the lambda abstraction in the next proof term.
The `apply` commands then correspond to building the application of the theorem to its arguments.
-/

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

/- Here is a useful trick: if you start writing the proof term `fun a b aleb ↦ _` using an
underscore where the rest of the expression should go, Lean will flag an error, indicating that it
can’t guess the value of that expression. If you check the Lean Goal window in VS Code or hover
over the squiggly error marker, Lean will show you the goal that the remaining expression has to
solve.
-/

-- EXERCISE: prove the following theorems with tatctics and proof terms
  -- First proof with tactics
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  -- Essentially we have to prove that c * f a ≤ c * f b
  -- We don't need the dsimp, we will handle this with the following apply
  apply mul_le_mul_of_nonneg_left _ nnc  -- We give nnc so we only have one hipothesis left
  exact mf aleb  -- Prove f a ≤ f b given f is monotonic and a ≤ b

  -- First proof with terms
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun _ _ aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

  -- Second proof with tactics
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  -- We need to prove that f (g a) ≤ f (g b) for monotonic f and g and a ≤ b
  apply mf  -- Given f monotonic, the new goal is to prove g a ≤ g b
  apply mg  -- Given g monotonic, the new goal is to prove a ≤ b
  exact aleb  -- Easy!

  -- Second proof with terms
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun _ _ aleb ↦ mf (mg aleb)


/- Here are some more examples. A function f from ℝ to ℝ is said to be even if f(-x) = f(x) for
every x, and odd if f(-x) = -f(x) for every x. The following example defines these two notions
formally and establishes one fact about them.
-/

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]

-- EXERCISE: complete the following proofs
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [of, og, neg_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  -- rw [ef, og, neg_neg]
  rw [og, ← ef]

end

/- Mathlib includes a good library for manipulating sets. Recall that Lean does not use foundations
based on set theory, so here the word set has its mundane meaning of a collection of mathematical
objects of some given type α. If x has type α and s has type Set α, then x ∈ s is a proposition
that asserts that x is an element of s. If y has some different type β then the expression y ∈ s
makes no sense. Here “makes no sense” means “has no type hence Lean does not accept it as a
well-formed statement”. This contrasts with Zermelo-Fraenkel set theory for instance where
a ∈ b is a well-formed statement for every mathematical objects a and b. For instance `sin ∈ cos`
is a well-formed statement in ZF. This defect of set theoretic foundations is an important
motivation for not using it in a proof assistant which is meant to assist us by detecting
meaningless expressions. In Lean `sin` has type `ℝ → ℝ` and `cos` has type `ℝ → ℝ` which is not
equal to `Set (ℝ → ℝ)`, even after unfolding definitions, so the statement `sin ∈ cos` makes no
sense. One can also use Lean to work on set theory itself. For instance the independence of the
continuum hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a
meta-theory of set theory is completely beyond the scope of this book.

If s and t are of type Set α, then the subset relation s ⊆ t is defined to mean
`∀ {x : α}, x ∈ s → x ∈ t`. The variable in the quantifier is marked implicit so that given
`h : s ⊆ t` and `h' : x ∈ s`, we can write h h' as justification for x ∈ t. The following example
provides a tactic proof and a proof term justifying the reflexivity of the subset relation.
-/

section
variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

-- EXERCISE: prove the transitivity of the subset relation
theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := fun rsubs ssubt x xinr ↦ ssubt (rsubs xinr)

end

/- Just as we defined `FnUb` for functions, we can define `SetUb s a` to mean that a is an upper
bound on the set s, assuming s is a set of elements of some type that has an order associated with
it.
-/

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- EXERCISE: prove that if a is a bound on s and a ≤ b, then b is a bound on s as well
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xins
  apply le_trans (h x xins) h'

  -- Sme with a proof term
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := fun x xins ↦ le_trans (h x xins) h'

end

/- We close this section with one last important example. A function f is said to be injective if
for every x₁ and x₂, if f(x₁) = f(x₂) then x₁ = x₂. Mathlib defines `Function.Injective f` with x₁
and x₂ implicit. The next example shows that, on the real numbers, any function that adds a
constant is injective.
-/

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

-- EXERCISE: show that multiplication by a nonzero constant is also injective
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

-- EXERCISE: show the composition of two injective functions is also injective
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h
