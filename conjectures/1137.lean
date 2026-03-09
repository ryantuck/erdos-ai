import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1137

Let $d_n = p_{n+1} - p_n$, where $p_n$ denotes the $n$th prime. Is it true that
$$\frac{\max_{n < x} d_n d_{n-1}}{(\max_{n < x} d_n)^2} \to 0$$
as $x \to \infty$?

Reference: [Va99, 1.2]
https://www.erdosproblems.com/1137
-/

/-- The nth prime (0-indexed): p 0 = 2, p 1 = 3, p 2 = 5, … -/
noncomputable def nthPrime : ℕ → ℕ := sorry

axiom nthPrime_prime : ∀ n, Nat.Prime (nthPrime n)
axiom nthPrime_strictMono : StrictMono nthPrime

/-- Prime gap: d n = p(n+1) - p(n). -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Product of consecutive prime gaps: d(n) * d(n-1), for n ≥ 1. -/
noncomputable def consecutiveGapProduct (n : ℕ) : ℕ :=
  primeGap n * primeGap (n - 1)

/-- Maximum of d(n) * d(n-1) for 1 ≤ n < x. -/
noncomputable def maxConsecutiveGapProduct (x : ℕ) : ℕ :=
  ((Finset.range x).filter (· ≥ 1)).sup consecutiveGapProduct

/-- Maximum of d(n) for n < x. -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  (Finset.range x).sup primeGap

/--
Erdős Problem #1137 [Va99, 1.2]:

Let d_n = p_{n+1} - p_n where p_n is the nth prime. Is it true that
  max_{n < x} (d_n · d_{n-1}) / (max_{n < x} d_n)² → 0
as x → ∞?

Informally, consecutive large prime gaps should not cluster: the product
of two adjacent gaps should be negligible compared to the square of the
largest gap.
-/
theorem erdos_problem_1137 :
    Filter.Tendsto
      (fun x : ℕ =>
        (maxConsecutiveGapProduct x : ℝ) / ((maxPrimeGap x : ℝ) ^ 2))
      atTop (nhds 0) :=
  sorry

end
