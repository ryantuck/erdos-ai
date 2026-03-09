import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open BigOperators Finset

/--
The harmonic sum over the interval of natural numbers {a, a+1, …, b}.
-/
noncomputable def harmonicInterval (a b : ℕ) : ℝ :=
  ∑ n ∈ Icc a b, (1 : ℝ) / (n : ℝ)

/--
Erdős Problem #288 [ErGr80]:

Is it true that there are only finitely many pairs of intervals I₁, I₂ such that
  ∑_{n₁ ∈ I₁} 1/n₁ + ∑_{n₂ ∈ I₂} 1/n₂ ∈ ℕ?

For example, 1/3 + 1/4 + 1/5 + 1/6 + 1/20 = 1 (where I₁ = {3,4,5,6}, I₂ = {20}).
-/
theorem erdos_problem_288 :
    Set.Finite {p : (ℕ × ℕ) × (ℕ × ℕ) |
      let (a₁, b₁) := p.1
      let (a₂, b₂) := p.2
      1 ≤ a₁ ∧ a₁ ≤ b₁ ∧ 1 ≤ a₂ ∧ a₂ ≤ b₂ ∧
      ∃ k : ℕ, 0 < k ∧ harmonicInterval a₁ b₁ + harmonicInterval a₂ b₂ = (k : ℝ)} :=
  sorry
