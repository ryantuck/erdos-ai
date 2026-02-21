import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Classical Filter Topology

noncomputable section

/-- A positive integer n has two divisors d₁, d₂ with d₁ < d₂ < 2 * d₁. -/
def HasCloseConsecutiveDivisors (n : ℕ) : Prop :=
  ∃ d₁ d₂ : ℕ, d₁ ∣ n ∧ d₂ ∣ n ∧ d₁ < d₂ ∧ d₂ < 2 * d₁

/--
Erdős Problem #144 [Er61, Er77c, Er79, Er79e, ErGr80, Er81h, Er82e, Er85e, Er97c, Er98]:
The density of integers which have two divisors d₁, d₂ such that d₁ < d₂ < 2*d₁
exists and is equal to 1.

Formally, writing A(N) for the number of integers n with 1 ≤ n ≤ N which have
two divisors d₁ < d₂ < 2*d₁, we have A(N)/N → 1 as N → ∞.

Proved by Maier and Tenenbaum [MaTe84].
-/
theorem erdos_problem_144 :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range N).filter (fun n => HasCloseConsecutiveDivisors (n + 1))).card : ℝ) /
        (N : ℝ))
      atTop
      (𝓝 (1 : ℝ)) :=
  sorry

end
