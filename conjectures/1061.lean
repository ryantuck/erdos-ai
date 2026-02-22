import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open ArithmeticFunction
open scoped ArithmeticFunction.sigma
open Filter

/-!
# Erdős Problem #1061

How many solutions are there to σ(a) + σ(b) = σ(a+b) with a+b ≤ x,
where σ is the sum of divisors function? Is it ∼ cx for some constant c > 0?

A question of Erdős reported in problem B15 of Guy's collection [Gu04].
-/

/-- The number of ordered pairs (a, b) with a ≥ 1, b ≥ 1, a + b ≤ x, and
    σ(a) + σ(b) = σ(a + b), where σ denotes the sum-of-divisors function. -/
noncomputable def sigmaAdditivityCount (x : ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun p : ℕ × ℕ =>
      0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 ≤ x ∧
      sigma 1 p.1 + sigma 1 p.2 = sigma 1 (p.1 + p.2))
    (Finset.range x ×ˢ Finset.range x))

/--
Erdős Problem #1061 [Gu04]:

The number of solutions to σ(a) + σ(b) = σ(a + b) with a + b ≤ x
is asymptotically cx for some constant c > 0.

Formulated as: there exists c > 0 such that
  sigmaAdditivityCount(x) / x → c as x → ∞.
-/
theorem erdos_problem_1061 :
    ∃ c : ℝ, c > 0 ∧
      Tendsto (fun x : ℕ => (sigmaAdditivityCount x : ℝ) / (x : ℝ))
        atTop (nhds c) :=
  sorry

end
