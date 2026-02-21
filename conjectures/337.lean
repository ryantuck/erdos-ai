import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology BigOperators Classical

noncomputable section

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset337 (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ∃ a ∈ A, ∃ b ∈ A, n = a + b}

/-- The set of all sums of exactly `k` elements from `A` (with repetition). -/
def exactSumset337 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- `A ⊆ ℕ` is an additive basis of order `r` if every sufficiently large
    natural number is the sum of at most `r` elements from `A`. -/
def IsAdditiveBasis337 (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ k ≤ r, n ∈ exactSumset337 A k

/-- Count of elements of `A` in `{0, 1, ..., N}`. -/
noncomputable def countInRange337 (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/--
Erdős Problem #337 [ErGr80, ErGr80b]:

Let A ⊆ ℕ be an additive basis (of any finite order) such that
|A ∩ {1,...,N}| = o(N). Is it true that
  lim_{N→∞} |(A+A) ∩ {1,...,N}| / |A ∩ {1,...,N}| = ∞ ?

The answer is no. A counterexample was provided by Turjányi [Tu84].
This was generalised (replacing A+A by the h-fold sumset hA for any
h ≥ 2) by Ruzsa and Turjányi [RT85].

Formalized as the negation (disproved): there exists an additive
basis A of some finite order with |A ∩ {1,...,N}| = o(N) such that
the ratio |(A+A) ∩ {1,...,N}| / |A ∩ {1,...,N}| does NOT tend to ∞.
-/
theorem erdos_problem_337 :
    ∃ (A : Set ℕ),
      (∃ r : ℕ, IsAdditiveBasis337 A r) ∧
      Tendsto (fun N => (countInRange337 A N : ℝ) / (N : ℝ)) atTop (nhds 0) ∧
      ¬ Tendsto (fun N => (countInRange337 (sumset337 A) N : ℝ) /
          (countInRange337 A N : ℝ)) atTop atTop :=
  sorry

end
