import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

open Classical

/-!
# Erdős Problem #292 (Proved)

Let A be the set of n ∈ ℕ such that there exist 1 ≤ m₁ < ⋯ < mₖ = n with
∑ 1/mᵢ = 1. Does A have density 1?

Straus observed that A is closed under multiplication. Furthermore, A does
not contain any prime power.

Proved by Martin [Ma00]: Yes, A has density 1. If B = ℕ \ A then
  |B ∩ [1,x]| / x ≍ log log x / log x,
and B consists essentially of small multiples of prime powers.
-/

/-- A positive integer n is Egyptian representable if there exists a finite set
    of distinct positive integers with maximum element n whose reciprocals sum to 1.
    That is, there exist 1 ≤ m₁ < ⋯ < mₖ = n with ∑ 1/mᵢ = 1. -/
def IsEgyptianRepresentable (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, n ∈ S ∧ (∀ m ∈ S, 1 ≤ m) ∧ (∀ m ∈ S, m ≤ n) ∧
    (S.sum fun m => (1 : ℚ) / m) = 1

/-- Count of Egyptian representable numbers in {1, …, N}. -/
noncomputable def egyptianCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun n => IsEgyptianRepresentable n).card

/--
Erdős Problem #292 (Proved) [ErGr80, p.35]:

The set of positive integers n for which there exist 1 ≤ m₁ < ⋯ < mₖ = n
with ∑ 1/mᵢ = 1 has natural density 1. Equivalently, for all ε > 0, the
count of such n in {1, …, N} satisfies |A ∩ [1,N]| / N ≥ 1 - ε for all
sufficiently large N.

Proved by Martin [Ma00], who showed the complementary set B = ℕ \ A satisfies
|B ∩ [1,x]| / x ≍ log log x / log x.
-/
theorem erdos_problem_292 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (egyptianCount N : ℝ) / (N : ℝ) ≥ 1 - ε :=
  sorry
