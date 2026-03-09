import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Real.Basic

open Filter Topology

/--
Erdős Problem #243 [ErGr80, Er88c]:

Let 1 ≤ a₁ < a₂ < ⋯ be a sequence of positive integers such that
  lim_{n → ∞} a(n) / a(n-1)² = 1
and ∑ 1/a(n) ∈ ℚ. Then for all sufficiently large n,
  a(n) = a(n-1)² - a(n-1) + 1.

A sequence satisfying this recurrence is known as Sylvester's sequence (OEIS A000058).
-/
theorem erdos_problem_243
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict_mono : StrictMono a)
    (ha_limit : Tendsto (fun n => (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (nhds 1))
    (ha_rational : ∃ q : ℚ, HasSum (fun n => (1 : ℝ) / (a n : ℝ)) (q : ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, a (n + 1) = (a n) ^ 2 - a n + 1 :=
  sorry
