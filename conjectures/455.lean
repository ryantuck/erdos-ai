import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Basic

open Filter

/--
A strictly increasing sequence of primes with non-decreasing gaps:
q(0) < q(1) < q(2) < ⋯ are all prime and q(n+1) - q(n) ≥ q(n) - q(n-1) for all n ≥ 1.
-/
structure IncreasingGapPrimeSeq (q : ℕ → ℕ) : Prop where
  prime : ∀ n, Nat.Prime (q n)
  strictMono : StrictMono q
  gapNonDecreasing : ∀ n, q (n + 2) - q (n + 1) ≥ q (n + 1) - q n

/--
Erdős Problem #455 [ErGr80,p.91]:

Let q₁ < q₂ < ⋯ be a sequence of primes such that q_{n+1} - qₙ ≥ qₙ - q_{n-1}.
Must lim_{n→∞} qₙ/n² = ∞?

Richter [Ri76] proved that liminf qₙ/n² > 0.352⋯.
-/
theorem erdos_problem_455
    (q : ℕ → ℕ)
    (hq : IncreasingGapPrimeSeq q) :
    Tendsto (fun n => (q n : ℝ) / (n : ℝ) ^ 2) atTop atTop :=
  sorry
