import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Defs

noncomputable section

open Real Finset Filter Topology Classical

/--
Count of positive integers m ≤ N having at least one divisor d
in the open interval (n, 2n).
-/
def countWithDivisor (n N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m =>
    ((Finset.Ioo n (2 * n)).filter (fun d => d ∣ m)).Nonempty)).card

/--
Count of positive integers m ≤ N having exactly r divisors d
in the open interval (n, 2n).
-/
def countWithExactDivisors (r n N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun m =>
    ((Finset.Ioo n (2 * n)).filter (fun d => d ∣ m)).card = r)).card

/--
The constant α = 1 - (1 + log(log 2)) / log 2 ≈ 0.08607,
appearing in the growth rate of δ(n).
-/
def erdos446Alpha : ℝ := 1 - (1 + Real.log (Real.log 2)) / Real.log 2

/--
Erdős Problem #446, Part 1 (Ford's Theorem on growth rate of δ(n)):

Let δ(n) denote the natural density of integers which are divisible by some
integer in (n, 2n). Ford [Fo08] determined the exact growth rate:

  δ(n) ≍ 1 / ((log n)^α · (log log n)^{3/2})

where α = 1 - (1 + log log 2) / log 2 ≈ 0.08607.

Background:
- Besicovitch [Be34] proved lim inf δ(n) = 0.
- Erdős [Er35] proved δ(n) = o(1).
- Erdős [Er60] proved δ(n) = (log n)^{-α + o(1)}.
- Tenenbaum [Te84] refined Erdős's estimate.
- Ford [Fo08] determined the exact growth rate.

This is formalized as: there exist constants C₁, C₂ > 0 such that for all
sufficiently large n, the proportion of integers ≤ N with a divisor in (n, 2n)
converges (as N → ∞) to a value δ(n) satisfying
  C₁ / f(n) ≤ δ(n) ≤ C₂ / f(n)
where f(n) = (log n)^α · (log log n)^{3/2}.
-/
theorem erdos_problem_446_growth_rate :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
        ∃ δ : ℝ,
          Filter.Tendsto (fun N : ℕ => (countWithDivisor n N : ℝ) / (N : ℝ))
            atTop (nhds δ) ∧
          C₁ / ((Real.log (n : ℝ)) ^ erdos446Alpha *
            (Real.log (Real.log (n : ℝ))) ^ ((3 : ℝ) / 2)) ≤ δ ∧
          δ ≤ C₂ / ((Real.log (n : ℝ)) ^ erdos446Alpha *
            (Real.log (Real.log (n : ℝ))) ^ ((3 : ℝ) / 2)) :=
  sorry

/--
Erdős Problem #446, Part 2 (Ford's disproof of δ₁(n) = o(δ(n))):

Erdős conjectured that δ₁(n) = o(δ(n)), where δ₁(n) is the density of integers
with exactly one divisor in (n, 2n). Ford [Fo08] disproved this, showing more
generally that for each r ≥ 1, δ_r(n) ≫_r δ(n), where δ_r(n) is the density
of integers with exactly r divisors in (n, 2n).

This is formalized as: for each r ≥ 1, there exists c > 0 such that for all
sufficiently large n, the natural density δ_r(n) satisfies δ_r(n) ≥ c · δ(n).
-/
theorem erdos_problem_446_disproof :
    ∀ r : ℕ, 0 < r →
      ∃ c : ℝ, 0 < c ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
          ∃ δ δ_r : ℝ,
            Filter.Tendsto (fun N : ℕ => (countWithDivisor n N : ℝ) / (N : ℝ))
              atTop (nhds δ) ∧
            Filter.Tendsto (fun N : ℕ => (countWithExactDivisors r n N : ℝ) / (N : ℝ))
              atTop (nhds δ_r) ∧
            δ_r ≥ c * δ :=
  sorry
