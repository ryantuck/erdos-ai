import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open Finset BigOperators

namespace Erdos1129

/-- The Lagrange basis polynomial l_k(x) for nodes indexed by Fin n.
    l_k(x) = ∏_{i ≠ k} (x - nodes i) / (nodes k - nodes i) -/
def lagrangeBasis {n : ℕ} (nodes : Fin n → ℝ) (k : Fin n) (x : ℝ) : ℝ :=
  ∏ i ∈ univ.filter (· ≠ k), (x - nodes i) / (nodes k - nodes i)

/-- The Lebesgue function: L(x) = ∑_k |l_k(x)| -/
def lebesgueFunction {n : ℕ} (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k, |lagrangeBasis nodes k x|

/-- The Lebesgue constant: Λ(nodes) = sup_{x ∈ [-1,1]} ∑_k |l_k(x)| -/
def lebesgueConstant {n : ℕ} (nodes : Fin n → ℝ) : ℝ :=
  sSup ((lebesgueFunction nodes) '' (Set.Icc (-1 : ℝ) 1))

/-- Nodes are valid: strictly increasing and in [-1, 1]. -/
def ValidNodes {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  StrictMono nodes ∧ ∀ i, nodes i ∈ Set.Icc (-1 : ℝ) 1

/-- The boundary sequence for the equioscillation property: -1, then the n nodes
    in order, then 1, giving n + 2 points partitioning [-1, 1] into n + 1
    subintervals. -/
def boundary {n : ℕ} (nodes : Fin n → ℝ) : Fin (n + 2) → ℝ :=
  fun i =>
    if h₁ : i.val = 0 then -1
    else if h₂ : i.val ≤ n then nodes ⟨i.val - 1, by omega⟩
    else 1

/-- The equioscillation property: the local maximum of the Lebesgue function is the
    same on each of the n + 1 subintervals [b_i, b_{i+1}]. -/
def HasEquioscillation {n : ℕ} (nodes : Fin n → ℝ) : Prop :=
  ∀ i j : Fin (n + 1),
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (boundary nodes ⟨i.val, by omega⟩)
               (boundary nodes ⟨i.val + 1, by omega⟩))) =
    sSup ((lebesgueFunction nodes) ''
      (Set.Icc (boundary nodes ⟨j.val, by omega⟩)
               (boundary nodes ⟨j.val + 1, by omega⟩)))

/--
Erdős Problem #1129 (Proved by Kilgore [Ki77] and de Boor–Pinkus [dBPi78]):

For x₁, ..., xₙ ∈ [-1,1], let l_k(x) = ∏_{i≠k}(x-xᵢ)/(x_k-xᵢ) be the
Lagrange basis polynomials and Λ = max_{x∈[-1,1]} ∑_k |l_k(x)| the Lebesgue
constant. Erdős and Bernstein conjectured that the minimising nodes are unique
and characterised by the equioscillation property: if
-1 = x₀ < x₁ < ··· < xₙ < x_{n+1} = 1 then
max_{x∈[xᵢ,x_{i+1}]} ∑_k |l_k(x)| is the same for all 0 ≤ i ≤ n.

Kilgore proved Λ is minimised only when equioscillation holds.
De Boor and Pinkus proved the minimising configuration is unique.
-/
theorem erdos_problem_1129 (n : ℕ) (hn : 2 ≤ n) :
    ∃ opt : Fin n → ℝ, ValidNodes opt ∧
      -- opt achieves the minimum Lebesgue constant
      (∀ nodes : Fin n → ℝ, ValidNodes nodes →
        lebesgueConstant opt ≤ lebesgueConstant nodes) ∧
      -- the minimiser is unique (among strictly increasing configurations)
      (∀ nodes : Fin n → ℝ, ValidNodes nodes →
        lebesgueConstant nodes = lebesgueConstant opt → nodes = opt) ∧
      -- the minimiser satisfies the equioscillation property
      HasEquioscillation opt :=
  sorry

end Erdos1129
