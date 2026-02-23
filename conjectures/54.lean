import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Set.Basic

open Finset Real

attribute [local instance] Classical.propDecidable

/--
A set A of natural numbers is Ramsey 2-complete if for every 2-coloring of ℕ,
all sufficiently large natural numbers can be represented as a sum of distinct
elements of A that all receive the same color.
-/
def IsRamsey2Complete (A : Set ℕ) : Prop :=
  ∀ (χ : ℕ → Fin 2),
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      ∃ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A ∧
        (∃ c : Fin 2, ∀ x ∈ S, χ x = c) ∧
        S.sum id = n

/--
Erdős Problem #54 (resolved by Conlon, Fox, and Pham [2021]):
There exists a Ramsey 2-complete set A of positive integers and a constant c > 0
such that |A ∩ {1,...,N}| ≤ c · (log N)² for all sufficiently large N.

This improves the upper bound (2 log₂ N)³ of Burr and Erdős, matching the
lower bound order of (log N)².
-/
theorem erdos_problem_54 :
    ∃ (A : Set ℕ),
      IsRamsey2Complete A ∧
        ∃ c : ℝ, c > 0 ∧
          ∃ N₀ : ℕ, ∀ N ≥ N₀,
            (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤
              c * (Real.log (N : ℝ)) ^ 2 :=
  sorry
