import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open MeasureTheory Finset Filter BigOperators

noncomputable section

/-!
# Erdős Problem #1131

For x₁, ..., xₙ ∈ [-1,1], define the Lagrange basis polynomials
  l_k(x) = ∏_{i≠k} (x - xᵢ) / (x_k - xᵢ),
so that l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

What is the minimal value of
  I(x₁, ..., xₙ) = ∫₋₁¹ ∑_k |l_k(x)|² dx?

In particular, is it true that min I = 2 - (1 + o(1)) / n?

Erdős, Szabados, Varma, and Vértesi [ESVV94] proved that
  2 - O((log n)² / n) ≤ min I ≤ 2 - 2/(2n-1),
where the upper bound is witnessed by the roots of the integral of the
Legendre polynomial.
-/

/-- The Lagrange basis polynomial l_k(x) for nodes `nodes : Fin n → ℝ` at index k:
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i). -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The L² functional I(x₁,...,xₙ) = ∫₋₁¹ ∑_k l_k(x)² dx. -/
def lagrangeL2 {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, ∑ k : Fin n, lagrangeBasis nodes k x ^ 2

/-- The minimum of the L² functional over all choices of n distinct nodes in [-1, 1]. -/
def minLagrangeL2 (n : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ nodes : Fin n → ℝ,
    Function.Injective nodes ∧
    (∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1) ∧
    v = lagrangeL2 nodes}

/--
Erdős Problem #1131:
For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k} (x - xᵢ)/(x_k - xᵢ) be the
Lagrange basis polynomials. The conjecture asks whether the minimum of
I(x₁,...,xₙ) = ∫₋₁¹ ∑_k |l_k(x)|² dx satisfies min I = 2 - (1 + o(1))/n,
i.e., n · (2 - min I) → 1 as n → ∞.
-/
theorem erdos_problem_1131 :
    Tendsto (fun n : ℕ => (n : ℝ) * (2 - minLagrangeL2 n)) atTop (nhds 1) :=
  sorry

end
