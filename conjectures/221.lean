import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open Finset Real

attribute [local instance] Classical.propDecidable

/--
Erdős Problem #221:
Is there a set A ⊆ ℕ such that |A ∩ {1,...,N}| ≪ N/log N and every
sufficiently large integer can be written as 2^k + a for some k ≥ 0 and a ∈ A?

The answer is yes, proved by Ruzsa [1972].
-/
theorem erdos_problem_221 :
    ∃ (A : Set ℕ),
      (∃ (C : ℝ), C > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Icc 1 N).filter (fun n => n ∈ A)).card : ℝ) ≤ C * ↑N / Real.log ↑N) ∧
      (∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∃ k : ℕ, ∃ a ∈ A, n = 2 ^ k + a) :=
  sorry
