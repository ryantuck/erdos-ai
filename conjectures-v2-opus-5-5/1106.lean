-- [AI-Generated]: Erdős Problem 1106 — second-pass formalization
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

/-!
# Erdős Problem #1106

*Source:* [erdosproblems.com/1106](https://www.erdosproblems.com/1106) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
16 November 2025, captured 2026-03-09). [Ob1]

Let p(n) denote the partition function of n and let F(n) count the number
of distinct prime factors of ∏_{1≤k≤n} p(k).

Does F(n) → ∞ with n? Is F(n) > n for all sufficiently large n?

Asked by Erdős at Oberwolfach in 1986 [Ob1]. The first question (F(n) → ∞) was answered
affirmatively: Schinzel noted in the Oberwolfach problem book that it follows from the
asymptotic formula for p(n) and a result of Tijdeman [Ti73] ("This is not obvious";
details are given on page 69 of Erdős–Ivić [ErIv90]). Schinzel and Wirsing [ScWi87]
proved F(n) ≫ log n. Ono [On00] proved that every prime divides p(n) for some n ≥ 1;
the page adds "indeed this holds, for any fixed prime, for a positive density set of n".
The second question remains open.

Observation: Ono's theorem alone also gives the first question, since each of the
first M primes divides some p(nᵢ), so F(n) ≥ M once n ≥ max nᵢ.

Computation (review scratch script, exact factorizations of p(1), …, p(700)): F(n) ≤ n
for every n ≤ 115 (F(115) = 115), and F(n) > n for every 116 ≤ n ≤ 700, with
F(700) = 1222. This is evidence for a "yes" to the second question, not a proof.

Tags: number theory. OEIS: A194259, A194260. The page records an upstream formalised
statement.

## References

* [Ob1] P. Erdős, _Oberwolfach Mathematical Problems, Volume 1_. Mathematisches
  Forschungsinstitut Oberwolfach (problem posed 1986).
* [Ti73] Tijdeman, R., _On integers with many small prime factors_. Compositio Math.
  (1973), 319–330.
* [ErIv90] Erdős, P. and Ivić, A. (1990), p. 69. (Stub: no bibliographic data recovered.)
* [ScWi87] Schinzel, A. and Wirsing, E. (1987). (Stub: no bibliographic data recovered.)
* [On00] Ono, K. (2000). (Stub: no bibliographic data recovered.)

(Provenance: [Ob1] from the original pipeline's fetch of `erdosproblems.com/latex/854` and
[Ti73] from `/latex/240`, both citing the same keys. The authors and years of the three
stubs are as named in the page's remarks.)
-/

/-- The number of partitions of n. -/
noncomputable def partitionCount1106 (n : ℕ) : ℕ :=
  Nat.card (Nat.Partition n)

/-- F(n) = number of distinct prime factors of ∏_{1≤k≤n} p(k).
(For example F(1), …, F(13) = 0, 1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 6. The product is
never 0, since p(k) ≥ 1.) -/
noncomputable def F1106 (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n, partitionCount1106 k).primeFactors.card

/--
Erdős Problem #1106 (part 1) (SOLVED — yes):
F(n) → ∞ as n → ∞.

Proved by Schinzel, using the asymptotic formula for p(n) and a result
of Tijdeman [Ti73]. Details in Erdős–Ivić [ErIv90, p.69]. Also a corollary of
[On00]; see `erdos_problem_1106.variants.ono`.
-/
theorem erdos_problem_1106_part1 :
    Filter.Tendsto (fun n => F1106 n) Filter.atTop Filter.atTop :=
  sorry

/--
Erdős Problem #1106 (part 2) (OPEN):
Is F(n) > n for all sufficiently large n?

Stated in the asked ("yes") direction as a direct assertion (this raw corpus has no
`answer()` elaborator); in `answer()` form it would be
`answer(sorry) ↔ ∀ᶠ n in atTop, F1106 n > n`.
-/
theorem erdos_problem_1106_part2 :
    ∀ᶠ n in Filter.atTop, F1106 n > n :=
  sorry

/-- Schinzel–Wirsing [ScWi87] (solved): F(n) ≫ log n. It is stated without logarithms as
`n ≤ 2 ^ (C · F(n))` for all large n, which is equivalent to `log₂ n ≤ C · F(n)`. -/
theorem erdos_problem_1106.variants.schinzel_wirsing :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ n in Filter.atTop, n ≤ 2 ^ (C * F1106 n) :=
  sorry

/-- Ono [On00] (solved): every prime divides p(n) for some n ≥ 1. (For 2 and 3 this is
immediate from p(2) = 2 and p(3) = 3.) -/
theorem erdos_problem_1106.variants.ono :
    ∀ q : ℕ, q.Prime → ∃ n : ℕ, 1 ≤ n ∧ q ∣ partitionCount1106 n :=
  sorry

end
