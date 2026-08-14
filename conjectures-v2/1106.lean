import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

/-!
# Erdős Problem #1106

Let p(n) denote the partition function of n and let F(n) count the number
of distinct prime factors of ∏_{1≤k≤n} p(k).

Does F(n) → ∞ with n? Is F(n) > n for all sufficiently large n?

Asked by Erdős at Oberwolfach in 1986 [Ob1]. The problem's overall status is
OPEN (the second question is open); the first question is settled:

Schinzel noted in the Oberwolfach problem book that F(n) → ∞ follows from the
asymptotic formula for p(n) and a result of Tijdeman [Ti73]. This is not
obvious; details are given in a paper of Erdős and Ivić (see page 69 of
[ErIv90]).

Schinzel and Wirsing [ScWi87] have proved F(n) ≫ log n.

Ono [On00] has proved that every prime divides p(n) for some n ≥ 1 (indeed
this holds, for any fixed prime, for a positive density set of n) — which
also implies F(n) → ∞.

## References

Bibliographic details below are honest stubs recovered from the archived
problem page and sibling files in this repo; entries marked "details not
recovered" await network access to erdosproblems.com/latex/1106.

- [Ob1] Oberwolfach problem session (1986).
- [Ti73] Tijdeman, R., _On integers with many small prime factors_.
  Compositio Math. (1973), 319–330.
- [ErIv90] Erdős, P. and Ivić, A. (1990). Paper giving (p. 69) the details of
  the deduction that F(n) → ∞. Title/journal details not recovered.
- [ScWi87] Schinzel, A. and Wirsing, E. (1987). Paper proving F(n) ≫ log n.
  Title/journal details not recovered.
- [On00] Ono, K. (2000). Paper proving that every prime divides p(n) for some
  n ≥ 1. Title/journal details not recovered.

https://www.erdosproblems.com/1106
Tags: number theory
Related OEIS sequences: A194259, A194260
-/

/-- The number of partitions of n. -/
noncomputable def partitionCount1106 (n : ℕ) : ℕ :=
  Nat.card (Nat.Partition n)

/-- F(n) = number of distinct prime factors of ∏_{1≤k≤n} p(k). -/
noncomputable def F1106 (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n, partitionCount1106 k).primeFactors.card

/--
Erdős Problem #1106 (part 1):
F(n) → ∞ as n → ∞.

Solved in the affirmative: Schinzel noted in the Oberwolfach problem book
that this follows from the asymptotic formula for p(n) and a result of
Tijdeman [Ti73]; this is not obvious, and details are given by Erdős–Ivić
(see page 69 of [ErIv90]). It also follows from Ono's theorem [On00]
(see `erdos_problem_1106_ono` below).
-/
theorem erdos_problem_1106_part1 :
    Filter.Tendsto (fun n => F1106 n) Filter.atTop Filter.atTop :=
  sorry

/--
Erdős Problem #1106 (part 2):
Is F(n) > n for all sufficiently large n?

This question is OPEN; the statement below asserts the conjectured
affirmative direction, following this corpus's convention for open yes/no
questions. Note F(n) > n genuinely fails for small n: p(1), …, p(6) =
1, 2, 3, 5, 7, 11 give F(n) = n − 1 for 1 ≤ n ≤ 6, so the "sufficiently
large" qualifier (encoded with `∀ᶠ … in atTop`) is essential. The best known
lower bound is F(n) ≫ log n, due to Schinzel and Wirsing [ScWi87].
-/
theorem erdos_problem_1106_part2 :
    ∀ᶠ n in Filter.atTop, F1106 n > n :=
  sorry

/--
Variant (Ono [On00]): every prime divides p(n) for some n ≥ 1.

Ono in fact proved more: for any fixed prime, the set of such n has positive
density (the density strengthening is not formalized here, as this file's
imports carry no density machinery). This result implies part 1, since every
prime eventually appears among the prime factors of ∏_{1≤k≤n} p(k).
-/
theorem erdos_problem_1106_ono (p : ℕ) (hp : p.Prime) :
    ∃ n : ℕ, 1 ≤ n ∧ p ∣ partitionCount1106 n :=
  sorry

end
