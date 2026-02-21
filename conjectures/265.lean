import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

/--
Erdős Problem #265 [ErGr80, p.64] [Er88c, p.104]:

Let 1 ≤ a₁ < a₂ < ⋯ be a strictly increasing sequence of integers with
aₙ ≥ 2 for all n. If both ∑ 1/aₙ and ∑ 1/(aₙ - 1) are rational, then
aₙ^(1/2^n) → 1 as n → ∞.

Cantor observed that aₙ = C(n,2) is such a sequence. Erdős believed that
aₙ^(1/n) → ∞ is possible (proved by Kovač–Tao [KoTa24]) but that
aₙ^(1/2^n) → 1 is necessary (still open). A folklore result establishes
that ∑ 1/aₙ is irrational whenever aₙ^(1/2^n) → ∞, so such a sequence
cannot grow faster than doubly exponentially. The remaining question is the
precise exponent possible.
-/
theorem erdos_problem_265
    (a : ℕ → ℕ)
    (ha_mono : StrictMono a)
    (ha_ge : ∀ n, 2 ≤ a n)
    (h_sum_rat : ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n : ℝ)) (q : ℝ))
    (h_shifted_sum_rat : ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / ((a n : ℝ) - 1)) (q : ℝ)) :
    Tendsto (fun n => ((a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (n : ℕ)))) atTop (nhds 1) :=
  sorry
