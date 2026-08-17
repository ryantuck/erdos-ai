import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

namespace Erdos1140

/-- The property that n - 2x² is prime for all x with 2x² < n. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/--
Erdős Problem #1140 [Va99, 1.5, Er85e] (Disproved):

Do there exist infinitely many n such that n - 2x² is prime for all x
with 2x² < n?

The known such n are 2, 5, 7, 13, 31, 61, 181, 199. Epure and Gica [EpGi10]
proved that the only such n ≡ 1 (mod 4) are 5, 13, 61, 181, and the only
such n ≡ 3 (mod 4) are 7, 31, 199 (with at most one exception, addressed
in [MoWi89]). This implies that, with at most one exception, the list above
is complete.

**Bibliography:**
- [Va99]: Vaughan, R. C., *The Hardy-Littlewood Method*, 2nd ed., Cambridge
  University Press, 1997. Section 1.5 discusses this problem.
- [EpGi10]: Epure, R. and Gica, A., "On a problem of Erdős concerning primes",
  2010.
- [MoWi89]: Mollin, R. A. and Williams, H. C., 1989. (Addresses the case
  n ≡ 3 (mod 4); full reference needed.)
- [Er85e]: Erdős, P., "Some recent problems on the prime factors of binomial
  coefficients", 1985 (or similar; as cited in Vaughan).

Tags: number theory
-/
theorem erdos_problem_1140 :
    answer(False) ↔ Set.Infinite {n : ℕ | AllShiftsArePrime n} :=
  sorry

end Erdos1140
