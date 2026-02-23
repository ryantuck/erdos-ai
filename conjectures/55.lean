import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Basic

open Finset Real

attribute [local instance] Classical.propDecidable

/--
A set A of natural numbers is Ramsey r-complete if for every r-coloring of ℕ,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of A that all receive the same color.
-/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ (χ : ℕ → Fin r),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin r, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem #55 (solved by Conlon, Fox, and Pham [2021]):
For every r ≥ 2, there exists an r-Ramsey complete set A such that
|A ∩ {1,...,N}| ≤ C · r · (log N)² for all sufficiently large N,
and this is best possible: there exists c > 0 such that if
|A ∩ {1,...,N}| ≤ c · r · (log N)² for all large N, then A
cannot be r-Ramsey complete.

Upper bound: for every r ≥ 2, there exists an r-Ramsey complete set
with counting function O(r · (log N)²). -/
theorem erdos_problem_55_upper :
    ∀ r : ℕ, 2 ≤ r →
      ∃ (A : Set ℕ),
        IsRamseyComplete A r ∧
          ∃ C : ℝ, C > 0 ∧
            ∃ N₀ : ℕ, ∀ N ≥ N₀,
              (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
                C * (r : ℝ) * (Real.log (N : ℝ)) ^ 2 :=
  sorry

/-- Lower bound: there exists c > 0 such that any set A with
    |A ∩ {1,...,N}| ≤ c · r · (log N)² for all large N
    cannot be r-Ramsey complete. -/
theorem erdos_problem_55_lower :
    ∀ r : ℕ, 2 ≤ r →
      ∃ c : ℝ, c > 0 ∧
        ∀ (A : Set ℕ),
          (∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (r : ℝ) * (Real.log (N : ℝ)) ^ 2) →
          ¬ IsRamseyComplete A r :=
  sorry
