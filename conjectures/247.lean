import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic

open Filter

noncomputable section

/--
Erdős Problem #247 [ErGr80, Er88c]:

Let 1 ≤ a₁ < a₂ < ⋯ be a strictly increasing sequence of positive integers
such that lim sup aₙ/n = ∞. Is ∑_{n=1}^∞ 1/2^{aₙ} transcendental?

Erdős proved the answer is yes under the stronger condition that
lim sup aₙ/kᵗ = ∞ for all t ≥ 1. He also conjectured that if aₙ > c·n²
then the sum is not the root of any quadratic polynomial.
-/
theorem erdos_problem_247
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict : StrictMono a)
    (ha_limsup : ∀ M : ℝ, ∃ᶠ n in atTop, M < (a n : ℝ) / n) :
    Transcendental ℤ (∑' n, (1 : ℝ) / 2 ^ a n) :=
  sorry

end
