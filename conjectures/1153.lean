import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Finset BigOperators

noncomputable section

namespace Erdos1153

/-!
# Erdős Problem #1153

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Let λ(x) = ∑_k |l_k(x)| (the Lebesgue function).

Is it true that, for any fixed -1 ≤ a < b ≤ 1,
  max_{x ∈ [a,b]} λ(x) > (2/π - o(1)) log n?

Bernstein proved this for a = -1 and b = 1, and Erdős improved this to
  max_{x ∈ [-1,1]} λ(x) > (2/π) log n - O(1).
This is best possible, since taking the xᵢ as the roots of the nth Chebyshev
polynomial yields max_{x ∈ [-1,1]} λ(x) < (2/π) log n + O(1).

The conjecture asks whether the same lower bound (up to o(1) in the coefficient)
holds when the maximum is restricted to any subinterval [a,b] ⊆ [-1,1].
-/

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: λ(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- Nodes are valid: pairwise distinct and in [-1, 1]. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  Function.Injective nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/--
Erdős Problem #1153:

For any fixed -1 ≤ a < b ≤ 1 and any ε > 0, there exists N such that for all
n ≥ N, for any choice of n distinct nodes x₁, ..., xₙ ∈ [-1,1],
  max_{x ∈ [a,b]} ∑_k |l_k(x)| > (2/π - ε) · log n.
-/
theorem erdos_problem_1153 (a b : ℝ) (hab : a < b) (ha : -1 ≤ a) (hb : b ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ nodes : Fin n → ℝ, ValidNodes nodes →
        ∃ x ∈ Set.Icc a b,
          lebesgueFunction nodes x > (2 / Real.pi - ε) * Real.log (n : ℝ) :=
  sorry

end Erdos1153
