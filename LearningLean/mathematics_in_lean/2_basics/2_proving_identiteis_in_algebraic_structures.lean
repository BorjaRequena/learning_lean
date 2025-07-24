import Mathlib

/-
** 2.2 Proving Identities in Algebraic Structures **
https://leanprover-community.github.io/mathematics_in_lean/C02_Basics.html#proving-identities-in-algebraic-structures

Mathematically, a ring consists of a collection of objects, R, operations + ×, and constants 0 and
1, and an operation x → -x such that:
- R with + is an abelian group, with 0 as the additive identity and negation as inverse
- Multiplication is associative with identity 1, and it distributes over addition

In Lean, the collection of objects is represented as a Type R.

Lean is good not only for proving things about concrete mathematical structures like the natural
numbers and the integers, but also for proving things about abstract structures, characterized
axiomatically, like rings. Moreover, Lean supports generic reasoning about both abstract and
concrete structures, and can be trained to recognize appropriate instances. So any theorem about
rings can be applied to concrete rings like the integers ℤ, the rational numbers ℚ, and the complex
numbers ℂ. t can also be applied to any instance of an abstract structure that extends rings, such
as any ordered ring or any field.
-/

-- Let's define a ring R in Lean
variable (R : Type*) [Ring R]

-- The axioms of the ring are the following:
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

-- Not all important properties of the real numbers hold in an arbitrary ring. For instance,
-- multiplication is not commutative in the ring of n×n real matrices. We can refine our definition
-- of the ring to explicitly say it is commutative.
section
variable (R : Type*) [CommRing R]

-- Now we can prove the theorems from the previous section using the `ring` tactic. As long as we
-- define the varaibles to belong to this ring
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

-- We will now learn how to use axioms from a ring to derive new facts. Since all of these will
-- already exist in Mathlib, we will add them to a new namespace `MyRing` to avoid any conflicts.
-- It's great to have gone through the functional programming in lean book to understand namespaces
namespace MyRing
variable {R : Type*} [Ring R]  -- Implicit argument R

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero
#check add_neg_cancel

end MyRing

-- Now let's add an existing useful theorem, and add it to the namespace `MyRing`
namespace MyRing  -- We can also add the theorem as `MyRing.neg_add_cancel_left`
variable {R : Type*} [Ring R]  -- Need to redeclare the variable, else it's taken as general Type u_1

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

#check neg_add_cancel_left

-- EXERCISE: prove the companion version using only the previous axioms and `neg_add_cancel_left`
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  -- rw [add_comm, add_comm a b, neg_add_cancel_left]  -- First attempt to prove it
  rw [add_assoc, add_neg_cancel, add_zero]  -- Fewer rewrites

#check neg_add_cancel_right

-- EXERCISE: prove the following theorems using only the preivous ones
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  -- rw [← add_zero b]
  -- rw [← add_neg_cancel a]
  -- rw [← add_assoc, add_comm, add_comm b a]
  -- rw [h]
  -- rw [neg_add_cancel_left]
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  -- rw [← add_zero a]
  -- rw [← add_neg_cancel b]
  -- rw [← add_assoc, h, add_neg_cancel_right]
  rw [add_comm a b] at h
  rw [add_comm c b] at h
  rw [add_left_cancel h]

/- When proving a theorem, Lean allows us to define a `have` tactic that introduces a new goal with
the same context as the original one. By proving this new hypothesis, we can then use it to prove
our original goal. This allows us to build modular proofs that are easier to understand, and can
guide the reasoning process.
-/

-- With these tactics, we can easily show that `a * 0 = 0` follows the ring axioms
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

-- Alternatively we can solve it with `apply`/`exact`, instead of `rw`. The `exact` tactic takes as
-- argument a proof term which completely proves the current goal, without creating any new goals.
example (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  exact add_left_cancel h

-- EXERCISE: since multiplication is not assumed to be commutative, we need to prove that 0 * a = 0
theorem zero_mul (a : R) : 0 * a = 0 := by
  have h: 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]


-- EXERCISE: prove the following theorems using only the facts about rings that we've extrablished
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel_left b a, add_comm b a, h, add_zero]

theorem neg_zero : (-0 : R) = 0 := by
-- (-0 : R) makes impossible for Lean to infer which 0 it means, so it defaults to `Nat`
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

end MyRing

-- In Lean, subtraction in a ring is provably equal to addition in the additive inverse
section
variable (R : Type*) [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

-- On the real numbers, it is defined this way:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

/- `rfl` is short for reflexibity. Presenting it a s a proof of a - b = a + -b forces Lean to unfold
the definition and recognize both sides being the same. This is an instance of what's known as a
deffinition equality in Lean's underlying logic. This means that not only can one rewrite with
`sub_eq_add_neg` to replace a - b = a + -b, but in some contexts with ℝ, you can use the two sides
of the equation interchangeably.
-/

namespace MyRing
variable {R : Type*} [Ring R]

-- EXCERCISE: prove the following `self_sub` theorem
theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

-- Lean knows that 1 + 1 = 2 in any ring
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- EXERCISE: we can use it to prove the `two_mul` theorem
theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

end MyRing

/- Facts about addition and negation that we established above do not need the full strength of
the ring axioms, or even commutativity of addition. The weaker notion of a *group* can be
axiomatized as follows
-/

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

/- It is conventional to use additive notation when the group operation is commutative, and
multiplicative notation otherwise. Lean defines a multiplicative version as well as the additive
version, as well as their abelian variants, AddCommGroup and CommGroup.
-/

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

end

-- EXERCISE: try proving the following facts about groups using only these axioms
namespace MyGroup
variable {G : Type*} [Group G]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]


theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹]
  rw [mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

end MyGroup

/- Explicitly invoking all of these lemmas is extremely tedious, so Mathlib provides tactics
similar to *ring* in order to cover most uses: *group* is for non-commutative multiplicative
groups, *abel* for abelian additive groups, and *noncomm_ring*  for non-commutative rings. It may
seem odd that the algebraic structures are called *Ring* and *CommRing* while the tactics are
named *noncomm_ring* and *ring*, respectively. This is mostly for historical reasons, although
commutative rings are more common so it's nice to have their tactic with a shorter name.
-/
