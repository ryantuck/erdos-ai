import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter BigOperators

noncomputable section

/-- The sum of divisors function σ(n) = ∑_{d | n} d. -/
def Nat.sumDivisors (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/--
Erdős Problem #823 [Er59c] [Er74b]:

Let α ≥ 1. Is there a sequence of positive integers n_k, m_k such that
n_k / m_k → α and σ(n_k) = σ(m_k) for all k ≥ 1, where σ is the sum of
divisors function?

The answer is yes, proved by Pollack [Po15b].
-/
theorem erdos_problem_823 (α : ℝ) (hα : α ≥ 1) :
    ∃ (n m : ℕ → ℕ), (∀ k, 0 < n k) ∧ (∀ k, 0 < m k) ∧
    (∀ k, Nat.sumDivisors (n k) = Nat.sumDivisors (m k)) ∧
    Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (nhds α) :=
  sorry

end
