import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
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

Status: OPEN per erdosproblems.com/1137 (page last edited 23 January 2026,
accessed 2026-03-09) — "This is open, and cannot be resolved with a finite
computation."

The problem is a yes/no question; following this corpus's convention for open
questions, the theorem below states the conjectured ("yes") direction as a
direct assertion. In styled question form it would be `answer(sorry) ↔ …`.

An upstream formalization exists at google-deepmind/formal-conjectures,
`FormalConjectures/ErdosProblems/1137.lean`; that file is the authoritative
styled artifact and is not present in this repository.

Tags: number theory, primes
Related OEIS sequences: A083550, A005250

Reference: [Va99, 1.2]
https://www.erdosproblems.com/1137

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §1.2.
-/

/-- The nth prime (0-indexed): p 0 = 2, p 1 = 3, p 2 = 5, … -/
noncomputable def nthPrime : ℕ → ℕ := Nat.nth Nat.Prime

/-- Every value of `nthPrime` is prime. (Formerly postulated as an axiom;
now a consequence of the concrete definition via `Nat.prime_nth_prime`.) -/
theorem nthPrime_prime : ∀ n, Nat.Prime (nthPrime n) :=
  Nat.prime_nth_prime

/-- `nthPrime` is strictly increasing. (Formerly postulated as an axiom;
now a consequence of the concrete definition, since the set of primes is
infinite.) -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- Prime gap: d n = p(n+1) - p(n). Since `nthPrime` is 0-indexed with
`nthPrime 0 = 2`, `primeGap n` is the source's $d_{n+1}$. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Product of consecutive prime gaps: d(n) * d(n-1), intended for n ≥ 1.
(At n = 0 the ℕ subtraction in `n - 1` truncates and this degenerates to
`primeGap 0 ^ 2`; that value is never used — `maxConsecutiveGapProduct`
filters to n ≥ 1.) -/
noncomputable def consecutiveGapProduct (n : ℕ) : ℕ :=
  primeGap n * primeGap (n - 1)

/-- Maximum of d(n) * d(n-1) for 1 ≤ n < x (0 if that range is empty,
`Finset.sup`'s bottom on ℕ). -/
noncomputable def maxConsecutiveGapProduct (x : ℕ) : ℕ :=
  ((Finset.range x).filter (· ≥ 1)).sup consecutiveGapProduct

/-- Maximum of d(n) for n < x (0 if x = 0, `Finset.sup`'s bottom on ℕ). -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  (Finset.range x).sup primeGap

/--
Erdős Problem #1137 [Va99, 1.2] (OPEN):

Let d_n = p_{n+1} - p_n where p_n is the nth prime. Is it true that
  max_{n < x} (d_n · d_{n-1}) / (max_{n < x} d_n)² → 0
as x → ∞?

Informally, consecutive large prime gaps should not cluster: the product
of two adjacent gaps should be negligible compared to the square of the
largest gap.

Stated here in the conjectured ("yes") direction, as this corpus does for
open yes/no questions; in styled question form it would be
`answer(sorry) ↔ Tendsto … (nhds 0)`.

Indexing note: with the 0-indexed `nthPrime`, `primeGap n` is the source's
$d_{n+1}$, so at each x both the numerator (max over source indices
$2 ≤ m ≤ x$ of $d_m d_{m-1}$) and the denominator (max over $1 ≤ m ≤ x$ of
$d_m$) equal the source's expressions at $x + 1$. This uniform shift leaves
the $x → ∞$ limit unchanged. At x = 0 the ratio is 0/0 = 0 by the ℝ division
convention, harmless under `atTop`.
-/
theorem erdos_problem_1137 :
    Filter.Tendsto
      (fun x : ℕ =>
        (maxConsecutiveGapProduct x : ℝ) / ((maxPrimeGap x : ℝ) ^ 2))
      atTop (nhds 0) :=
  sorry

end
