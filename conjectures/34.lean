import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin

open Finset BigOperators Equiv

/--
For a permutation σ of Fin n, the set of distinct consecutive sums.
A consecutive sum is ∑_{i ∈ [u,v]} (σ(i) + 1) for u ≤ v in Fin n,
corresponding to summing consecutive values of a permutation of {1,...,n}.
-/
noncomputable def consecutiveSums (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  ((Finset.univ (α := Fin n)) ×ˢ (Finset.univ (α := Fin n))).filter (fun p => p.1 ≤ p.2)
    |>.image (fun p => ∑ i ∈ Finset.Icc p.1 p.2, ((σ i).val + 1))

/--
Erdős Problem #34 (Disproved):
For any permutation π of {1,...,n}, let S(π) count the number of distinct
consecutive sums (sums of the form ∑_{u ≤ i ≤ v} π(i)).
The conjecture asks: is it true that S(π) = o(n²) for all π ∈ S_n?

This was disproved by Hegyvári (1986) and shown to be extremely false by
Konieczny (2015), who proved that a random permutation has ∼(1+e⁻²)/4 · n²
distinct consecutive sums.
-/
theorem erdos_problem_34 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ σ : Equiv.Perm (Fin n),
        ((consecutiveSums n σ).card : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
sorry
