import Mathlib

/-
** Sequences and Convergence **
https://leanprover-community.github.io/mathematics_in_lean/C03_Logic.html#sequences-and-convergence

We now have enough skills at our disposal to do some real mathematics. In Lean, we can represent a
sequence s₀, s₁, s₂, ... of real numbers as a function `s : ℕ → ℝ`. Such a sequence is said to
*converge* to a number `a` if for every `ε < 0` there is a point beyond which the sequence remains
within `ε` of `a`, that is, there is a number `N` such that for every `n ≥ N`, `|sₙ - a| < ε`. In
Lean, we can render this as follows:
-/

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

/- The notation `∀ ε > 0, ...` is a convenient abbreviation for `∀ ε, ε > 0 → ...`, and, similarly,
`∀ n ≥ N, ...` abbreviates `∀ n, n ≥ N →  ....` And remember that `ε > 0`, in turn, is defined as
`0 < ε`, and `n ≥ N` is defined as `N ≤ n`.

In this section, we’ll establish some properties of convergence. But first, we will discuss three
tactics for working with equality that will prove useful. The first, the `ext` tactic, gives us a
way of proving that two functions are equal. Let f(x) = x + 1 and g(x) = 1 + x be functions from
reals to reals. Then, of course, `f = g`, because they return the same value for every `x`. The
`ext` tactic enables us to prove an equation between functions by proving that their values are
the same at all the values of their arguments.
-/

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

/- We’ll see later that `ext` is actually more general, and also one can specify the name of the
variables that appear. For instance you can try to replace `ext` with `ext u v` in the above proof.
The second tactic, the `congr` tactic, allows us to prove an equation between two expressions by
reconciling the parts that are different:
-/

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

/- Here the `congr` tactic peels off the `abs` on each side, leaving us to prove `a = a - b + b`.

Finally, the `convert` tactic is used to apply a theorem to a goal when the conclusion of the
theorem doesn’t quite match. For example, suppose we want to prove `a < a * a` from `1 < a`. A
theorem in the library, `mul_lt_mul_right`, will let us prove `1 * a < a * a`. One possibility is
to work backwards and rewrite the goal so that it has that form. Instead, the `convert` tactic lets
us apply the theorem as it is, and leaves us with the task of proving the equations that are needed
to make the goal match.
-/

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

/-This example illustrates another useful trick: when we apply an expression with an underscore and
Lean can’t fill it in for us automatically, it simply leaves it for us as another goal.

The following shows that any constant sequence `a, a, a, …` converges.
-/

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  exact εpos

/- Lean has a tactic, `simp`, which can often save you the trouble of carrying out steps like
`rw [sub_self, abs_zero]` by hand. We will tell you more about it soon.

For a more interesting theorem, let’s show that if `s` converges to `a` and `t` converges to `b`,
then `fun n ↦ s n + t n` converges to `a + b`. It is helpful to have a clear pen-and-paper proof in
mind before you start writing a formal one. Given `ε` greater than `0`, the idea is to use the
hypotheses to obtain an `Ns` such that beyond that point, `s` is within `ε / 2` of `a`, and an `Nt`
such that beyond that point, `t` is within `ε / 2` of `b`. Then, whenever `n` is greater than or
equal to the maximum of `Ns` and `Nt`, the sequence `fun n ↦ s n + t n` should be within `ε` of
`a + b`. The following example begins to implement this strategy.
-/

-- EXERCISE: Finish off the following proof

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  -- Complete the proof from here onwards
  intro n nge
  have ngeNs : n ≥ Ns := le_of_max_le_left nge
  have ngeNt : n ≥ Nt := le_of_max_le_right nge
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)  -- `abs_add _ _` also works
    _ < ε / 2 + ε / 2 := by
      apply add_lt_add
      exact hs n ngeNs
      exact ht n ngeNt
    _ = ε := by linarith

/- As hints, you can use `le_of_max_le_left` and `le_of_max_le_right`, and `norm_num` can prove
`ε / 2 + ε / 2 = ε`. Also, it is helpful to use the `congr` tactic to show that
`|s n + t n - (a + b)|` is equal to `|(s n - a) + (t n - b)|`, since then you can use the triangle
inequality. Notice that we marked all the variables `s`, `t`, `a`, and `b` implicit because they
can be inferred from the hypotheses.

Proving the same theorem with multiplication in place of addition is tricky. We will get there by
proving some auxiliary statements first. The next proof shows that if `s` converges to `a`, then
`fun n ↦ c * s n` converges to `c * a`. It is helpful to split into cases depending on whether `c`
is equal to zero or not. We have taken care of the zero case, and we have left you to prove the
result with the extra assumption that `c` is nonzero.
-/

-- EXERCISE: Finish off the following proof

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  -- Complete the proof from here onwards
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n nge
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := by
      apply mul_lt_mul_of_pos_left
      exact hs n nge
      exact acpos
    _ = ε := by rw [mul_div_cancel₀ _ (ne_of_gt acpos)]

/- The next theorem is also independently interesting: it shows that a convergent sequence is
eventually bounded in absolute value.
-/

-- EXERCISE: finish off the following proof

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  -- Complete the proof from here onwards
  intro n nge
  calc
    |s n| = |s n - a + a| := by
      congr
      ring
    _ ≤ |s n - a| + |a| := abs_add (s n - a) a
    _ < |a| + 1 := by linarith [h n nge]

/- In fact, the theorem could be strengthened to assert that there is a bound `b` that holds for
all values of `n`. But this version is strong enough for our purposes, and we will see at the end
of this section that it holds more generally.

The next lemma is auxiliary: we prove that if `s` converges to `a` and `t` converges to `0`, then
`fun n ↦ s n * t n` converges to `0`. To do so, we use the previous theorem to find a `B` that
bounds `s` beyond some point `N₀`.
-/

-- EXERCISE: finish the following proof with the strategy that we have outlined

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  -- Complete the proof from here onwards
  use max N₀ N₁
  intro n nge
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left nge
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right nge
  calc
    |s n * t n - 0| = |s n * t n| := by rw [sub_zero]
    _ = |s n| * |t n| := by rw [← abs_mul]
    _ = |s n| * |t n - 0| := by rw [sub_zero]
    _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

/- If you have made it this far, congratulations! We are now within striking distance of our
theorem. The following proof finishes it off.
-/

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

-- EXERCISE: Fill out the following proof sketch

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    -- Prove this
    apply lt_of_le_of_ne
    · show 0 ≤ |a - b|
      exact abs_nonneg (a - b)
    · show 0 ≠ |a - b|
      intro h'
      apply abne
      apply eq_of_abs_sub_eq_zero h'.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    -- Prove this
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    -- Prove this
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b| := by
    -- Prove this
    calc
      |a - b| = |(-(s N - a)) + (s N - b)| := by
        congr
        ring
      _ ≤ |(-(s N - a))| + |s N - b| := abs_add (-(s N - a)) (s N - b)
      _ = |s N - a| + |s N - b| := by rw [abs_neg]
      _ < ε + ε := by linarith
      _ = |a - b| := by norm_num [ε]
  exact lt_irrefl _ this

/- We close the section with the observation that our proofs can be generalized. For example, the
only properties that we have used of the natural numbers is that their structure carries a partial
order with `min` and `max`. You can check that everything still works if you replace `ℕ` everywhere
by any linear order `α`:
-/

section

variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

/- In Section 11.1 (Filters), we will see that Mathlib has mechanisms for dealing with convergence
in vastly more general terms, not only abstracting away particular features of the domain and
codomain, but also abstracting over different types of convergence.
-/
