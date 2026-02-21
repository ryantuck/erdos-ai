import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators

/-- The set of all contiguous subsequence sums of a finite integer sequence.
    For a sequence a : Fin k → ℤ, this is {∑_{i=u}^{v} a_i : 0 ≤ u ≤ v < k}. -/
def contiguousSubSums {k : ℕ} (a : Fin k → ℤ) : Finset ℤ :=
  ((univ ×ˢ univ).filter (fun p : Fin k × Fin k => p.1 ≤ p.2)).image
    (fun p => ∑ i ∈ Icc p.1 p.2, a i)

/--
Erdős Problem #356 [ErGr80, p.58]:

Is there some c > 0 such that, for all sufficiently large n, there exist
integers a₁ < ··· < aₖ ≤ n such that there are at least cn² distinct integers
of the form ∑_{u≤i≤v} aᵢ (contiguous subsequence sums)?

Solved in the affirmative by Beker [Be23b].
-/
theorem erdos_problem_356 :
    ∃ c : ℝ, c > 0 ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ (k : ℕ) (a : Fin k → ℤ),
      StrictMono a ∧
      (∀ i : Fin k, a i ≤ ↑n) ∧
      (↑(contiguousSubSums a).card : ℝ) ≥ c * (↑n : ℝ) ^ 2 :=
  sorry
