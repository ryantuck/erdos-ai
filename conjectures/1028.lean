import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

noncomputable section

/-!
# Erdős Problem #1028

Let H(n) = min_f max_{X ⊆ {1,...,n}} |Σ_{x≠y∈X} f(x,y)|,
where f ranges over all functions f: {1,...,n}² → {-1,1}. Estimate H(n).

Erdős [Er63d] proved n/4 ≤ H(n) ≪ n^{3/2}.
Erdős and Spencer [ErSp71] proved that H(n) ≫ n^{3/2}.

Together these give H(n) = Θ(n^{3/2}).
-/

/-- The discrepancy sum of a ±1 function `f` over a subset `X` of `Fin n`:
    Σ_{x ≠ y ∈ X} f(x, y) over ordered pairs with x ≠ y. -/
def discrepancySum (n : ℕ) (f : Fin n → Fin n → ℤ) (X : Finset (Fin n)) : ℤ :=
  X.sum fun x => (X.filter (· ≠ x)).sum fun y => f x y

/--
Erdős Problem #1028 [Er63d][Er71,p.107]:

H(n) = Θ(n^{3/2}), where H(n) = min_f max_{X ⊆ {1,...,n}} |Σ_{x≠y∈X} f(x,y)|
and f ranges over all ±1 valued functions on pairs.

This is equivalent to two bounds:
- Lower bound (Erdős-Spencer [ErSp71]): every ±1 function f has some subset X
  with discrepancy at least C₁ · n^{3/2}.
- Upper bound (Erdős [Er63d]): there exists a ±1 function f such that all subsets
  have discrepancy at most C₂ · n^{3/2}.
-/
theorem erdos_problem_1028 :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    -- Lower bound: every ±1 function has a subset with large discrepancy
    (∀ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) →
      ∃ X : Finset (Fin n),
        C₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ |(discrepancySum n f X : ℝ)|) ∧
    -- Upper bound: there exists a ±1 function with all discrepancies bounded
    (∃ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) ∧
      ∀ X : Finset (Fin n),
        |(discrepancySum n f X : ℝ)| ≤ C₂ * (n : ℝ) ^ ((3 : ℝ) / 2)) :=
  sorry

end
