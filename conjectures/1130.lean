import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open Finset BigOperators

namespace Erdos1130

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: Λ(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- Nodes are valid: strictly increasing and in [-1, 1]. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- The boundary sequence: -1, then the n nodes in order, then 1,
    giving n + 2 points partitioning [-1, 1] into n + 1 subintervals. -/
def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The supremum of the Lebesgue function on the i-th subinterval
    [boundary(i), boundary(i+1)]. -/
def localMax {n : ℕ} (nodes : Fin n → ℝ) (i : Fin (n + 1)) : ℝ :=
  sSup ((lebesgueFunction nodes) ''
    (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
             (boundary nodes ⟨i.val + 1, by omega⟩)))

/--
Erdős Problem #1130 (Proved by de Boor and Pinkus [dBPi78]):

For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k}(x-xᵢ)/(x_k-xᵢ) be the
Lagrange basis polynomials (fundamental functions of Lagrange interpolation),
satisfying l_k(x_k) = 1 and l_k(xᵢ) = 0 for i ≠ k.

Set x₀ = -1 and x_{n+1} = 1. Define
  Υ(x₁,...,xₙ) = min_{0 ≤ i ≤ n} max_{x ∈ [xᵢ,x_{i+1}]} ∑_k |l_k(x)|.

The conjecture asks: is Υ(x₁,...,xₙ) ≪ log n?

This is true. It follows from the equioscillation result [1129] and the work
of de Boor and Pinkus that Υ(x₁,...,xₙ) ≤ (2/π) log n + O(1).
-/
theorem erdos_problem_1130 :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ), n ≥ 2 →
    ∀ (nodes : Fin n → ℝ), ValidNodes nodes →
    ∃ i : Fin (n + 1), localMax nodes i ≤ C * Real.log n :=
  sorry

end Erdos1130
