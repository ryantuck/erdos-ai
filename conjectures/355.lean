import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Bounds.Basic

open BigOperators Finset

/--
A sequence `a : ℕ → ℕ` is **lacunary** with ratio `λ` if `λ > 1` and
`a(n+1) / a(n) ≥ λ` for all `n`.
-/
def IsLacunary (a : ℕ → ℕ) (lam : ℝ) : Prop :=
  1 < lam ∧ StrictMono a ∧ (∀ n : ℕ, (a n : ℝ) * lam ≤ (a (n + 1) : ℝ))

/--
The set of finite subsums of the unit fractions 1/a(n):
  { ∑_{i ∈ S} 1/a(i) : S a finite set of indices }.
-/
def FiniteSubsums (a : ℕ → ℕ) : Set ℝ :=
  { x : ℝ | ∃ S : Finset ℕ, x = ∑ i ∈ S, (1 : ℝ) / (a i : ℝ) }

/--
Erdős Problem #355 [BlEr76, ErGr80]:

Is there a lacunary sequence A ⊆ ℕ (i.e., A = {a₁ < a₂ < ⋯} with
a_{n+1}/a_n ≥ λ for some λ > 1) such that the set of finite subsums
  { ∑_{a ∈ A'} 1/a : A' ⊆ A finite }
contains all rationals in some open interval?

Bleicher and Erdős conjectured the answer is no. In fact the answer is yes,
with any lacunarity constant λ ∈ (1,2) (though not λ = 2), as proved by
van Doorn and Kovač [DoKo25].
-/
theorem erdos_problem_355 :
    ∃ (a : ℕ → ℕ) (lam : ℝ),
      IsLacunary a lam ∧
      ∃ (lo hi : ℝ), lo < hi ∧
        ∀ q : ℚ, lo < (q : ℝ) → (q : ℝ) < hi → (q : ℝ) ∈ FiniteSubsums a :=
  sorry
