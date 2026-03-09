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

The first question (F(n) → ∞) was answered affirmatively by Schinzel, using
the asymptotic formula for p(n) and a result of Tijdeman. Schinzel and
Wirsing proved F(n) ≫ log n. The second question remains open.

https://www.erdosproblems.com/1106
Tags: number theory
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

Proved by Schinzel, using the asymptotic formula for p(n) and a result
of Tijdeman [Ti73]. Details in Erdős–Ivić [ErIv90].
-/
theorem erdos_problem_1106_part1 :
    Filter.Tendsto (fun n => F1106 n) Filter.atTop Filter.atTop :=
  sorry

/--
Erdős Problem #1106 (part 2):
Is F(n) > n for all sufficiently large n?
-/
theorem erdos_problem_1106_part2 :
    ∀ᶠ n in Filter.atTop, F1106 n > n :=
  sorry

end
