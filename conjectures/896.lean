import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Real

/--
F(A,B) counts the number of distinct products m = a·b (with a ∈ A, b ∈ B)
that have exactly one representation as such a product.
-/
def uniqueProductCount (A B : Finset ℕ) : ℕ :=
  ((A ×ˢ B).image (fun p => p.1 * p.2)).filter (fun m =>
    ((A ×ˢ B).filter (fun p => p.1 * p.2 = m)).card = 1) |>.card

/-!
# Erdős Problem #896

[Er72, p.81]: Estimate the maximum of F(A,B) as A, B range over all subsets
of {1,…,N}, where F(A,B) counts the number of m such that m = ab has exactly
one solution with a ∈ A and b ∈ B.

Van Doorn proved:
  (1 + o(1)) N²/log N ≤ max_{A,B} F(A,B) ≪ N²/((log N)^δ (log log N)^{3/2})
where δ = 1 - (1 + log log 2)/log 2 ≈ 0.086.

The lower bound shows the maximum is at least ~N²/log N. The open problem
is to determine the exact asymptotic order. We conjecture the lower bound
is tight: max F(A,B) = Θ(N²/log N).
-/

/-- Known lower bound (van Doorn): for any ε > 0 and all sufficiently large N,
    there exist A, B ⊆ {1,…,N} with F(A,B) ≥ (1-ε)·N²/log N. -/
theorem erdos_problem_896_lower :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ A B : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ B ⊆ Finset.Icc 1 N ∧
        (uniqueProductCount A B : ℝ) ≥ (1 - ε) * (N : ℝ) ^ 2 / Real.log (N : ℝ) :=
  sorry

/-- Open conjecture: max F(A,B) ≤ C·N²/log N for some absolute constant C,
    i.e., the lower bound gives the correct order of magnitude. -/
theorem erdos_problem_896 :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N →
        (uniqueProductCount A B : ℝ) ≤ C * (N : ℝ) ^ 2 / Real.log (N : ℝ) :=
  sorry
