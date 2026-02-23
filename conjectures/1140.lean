import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

namespace Erdos1140

/-- The property that n - 2x² is prime for all x with 2x² < n. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/--
Erdős Problem #1140 [Va99, 1.5] (Disproved):

Do there exist infinitely many n such that n - 2x² is prime for all x
with 2x² < n?

The known such n are 2, 5, 7, 13, 31, 61, 181, 199. Epure and Gica [EpGi10]
proved that the only such n ≡ 1 (mod 4) are 5, 13, 61, 181, and the only
such n ≡ 3 (mod 4) are 7, 31, 199 (with at most one exception).
This implies that, with at most one exception, the list above is complete.

Tags: number theory
-/
theorem erdos_problem_1140 :
    Set.Finite {n : ℕ | AllShiftsArePrime n} :=
  sorry

end Erdos1140
