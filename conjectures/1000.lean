import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #1000

Let A = {n₁ < n₂ < ⋯} be an infinite sequence of integers, and let φ_A(k)
count the number of 1 ≤ m ≤ n_k such that the fraction m/n_k does not have
denominator n_j for j < k when written in lowest form; equivalently,
n_k / gcd(m, n_k) ≠ n_j for all 1 ≤ j < k.

Is there a sequence A such that
  lim_{N → ∞} (1/N) ∑_{k ≤ N} φ_A(k)/n_k = 0?

Erdős believed no such sequence exists. This was solved by Haight [Ha] who
proved that such a sequence does exist (contrary to Erdős' expectations).
-/

/-- For a strictly increasing sequence `a : ℕ → ℕ` of positive integers,
    `phiA a k` counts the number of `1 ≤ m ≤ a k` such that
    `a k / gcd(m, a k) ≠ a j` for all `j < k`. -/
def phiA (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.Icc 1 (a k)).filter (fun m =>
    ∀ j < k, (a k) / Nat.gcd m (a k) ≠ a j)).card

/--
Erdős Problem #1000 [Er64b]:

There exists a strictly increasing sequence A = {n₁ < n₂ < ⋯} of positive
integers such that the Cesàro mean of φ_A(k)/n_k tends to 0:

  lim_{N → ∞} (1/N) ∑_{k ≤ N} φ_A(k)/n_k = 0.

Proved by Haight [Ha].
-/
theorem erdos_problem_1000 :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ i, 0 < a i) ∧
    Filter.Tendsto
      (fun N : ℕ => (∑ k ∈ Finset.range N, (phiA a k : ℝ) / (a k : ℝ)) / (N : ℝ))
      Filter.atTop (nhds 0) :=
  sorry

end
