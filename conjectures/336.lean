import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Set Filter Topology BigOperators

/-- The set of all sums of exactly `k` elements from `A` (with repetition allowed). -/
def exactSumset336 (A : Set ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ (f : Fin k → ℕ), (∀ i, f i ∈ A) ∧ n = ∑ i, f i}

/-- `A ⊆ ℕ` is an additive basis of order `r` if every sufficiently large natural number
    is the sum of at most `r` elements from `A`. -/
def IsAdditiveBasis336 (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∃ k ≤ r, n ∈ exactSumset336 A k

/-- `A` has exact order `k` if every sufficiently large natural number
    is the sum of exactly `k` elements from `A`. -/
def HasExactOrder336 (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, n ∈ exactSumset336 A k

/-- `h(r)` is the maximal `k` such that some basis of order `r` has exact order `k`.
    (Uses `sSup` on `ℕ`, which returns the maximum when the set is bounded above.) -/
noncomputable def h_basis336 (r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Set ℕ, IsAdditiveBasis336 A r ∧ HasExactOrder336 A k}

/--
Erdős Problem #336 [ErGr80, p.51]:

For r ≥ 2 let h(r) be the maximal finite k such that there exists a basis A ⊆ ℕ
of order r (every sufficiently large integer is the sum of at most r elements
from A) and exact order k (every sufficiently large integer is the sum of exactly
k elements from A).

Find the value of lim_{r→∞} h(r)/r².

Known bounds: 1/3 ≤ lim h(r)/r² ≤ 1/2 (lower bound due to Grekos, upper bound
due to Nash).
-/
theorem erdos_problem_336 :
    ∃ c : ℝ, 1/3 ≤ c ∧ c ≤ 1/2 ∧
      Filter.Tendsto (fun r : ℕ => (h_basis336 r : ℝ) / ((r : ℝ) ^ 2))
        Filter.atTop (nhds c) :=
  sorry
