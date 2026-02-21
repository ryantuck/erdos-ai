import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped Classical
open Finset BigOperators

/-- The signed sum of complex numbers z with signs ε ∈ {-1, 1}ⁿ (encoded as Bool). -/
noncomputable def signedSum {n : ℕ} (z : Fin n → ℂ) (ε : Fin n → Bool) : ℂ :=
  ∑ i : Fin n, (if ε i then (1 : ℂ) else (-1 : ℂ)) * z i

/--
Erdős Problem #395 (Proved by He, Juškevičius, Narayanan, and Spiro [HJNS24]):

If z₁, ..., zₙ ∈ ℂ with |zᵢ| = 1, then the probability that
|ε₁z₁ + ⋯ + εₙzₙ| ≤ √2, where εᵢ ∈ {-1, 1} uniformly at random,
is ≫ 1/n.

Formally: there exists c > 0 such that for all n ≥ 1 and all unit complex vectors
z : Fin n → ℂ, the number of sign patterns ε : Fin n → Bool for which
‖∑ εᵢzᵢ‖ ≤ √2 is at least c · 2ⁿ / n.

This is a reverse Littlewood-Offord problem. The bound 1/n is best possible,
as shown by taking zₖ = 1 for 1 ≤ k ≤ n/2 and zₖ = i otherwise.
-/
theorem erdos_problem_395 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (z : Fin n → ℂ),
    (∀ i, ‖z i‖ = 1) →
    c * (2 : ℝ) ^ n / (n : ℝ) ≤
      ((Finset.univ.filter (fun ε : Fin n → Bool =>
        ‖signedSum z ε‖ ≤ Real.sqrt 2)).card : ℝ) :=
  sorry
