import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #1074

Let S be the set of all m ≥ 1 such that there exists a prime p ≢ 1 (mod m)
such that p ∣ m! + 1. These are called 'EHS numbers' (after Erdős, Hardy,
and Subbarao). Does lim |S ∩ [1,x]| / x exist? What is it?

Similarly, let P be the set of all primes p such that there exists m ≥ 1
with p ≢ 1 (mod m) and p ∣ m! + 1. These are called 'Pillai primes'.
Does lim |P ∩ [1,x]| / π(x) exist? What is it?

A question of Erdős, Hardy, and Subbarao [HaSu02], who proved that both S
and P are infinite. The sequence S begins 8, 9, 13, 14, 15, 16, 17, ...
(OEIS A064164) and P begins 23, 29, 59, 61, 67, 71, ... (OEIS A063980).

Hardy and Subbarao conjectured the density of S is 1. For P, they noted the
relative density appears to be between 0.5 and 0.6, but speculated it should
tend to 1.
-/

/-- An EHS number is an m ≥ 1 such that there exists a prime p with p ≢ 1 (mod m)
    and p ∣ m! + 1. -/
def isEHSNumber (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ p, Nat.Prime p ∧ ¬(p ≡ 1 [MOD m]) ∧ p ∣ Nat.factorial m + 1

/-- A Pillai prime is a prime p such that there exists m ≥ 1 with p ≢ 1 (mod m)
    and p ∣ m! + 1. -/
def isPillaiPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m, 1 ≤ m ∧ ¬(p ≡ 1 [MOD m]) ∧ p ∣ Nat.factorial m + 1

/-- Count of EHS numbers in [1, x]. -/
noncomputable def countEHS (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun m => isEHSNumber m)).card

/-- Count of Pillai primes in [1, x]. -/
noncomputable def countPillaiPrimes (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun p => isPillaiPrime p)).card

/-- Prime counting function π(x). -/
noncomputable def primeCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun p => Nat.Prime p)).card

/--
Erdős Problem #1074, Part 1 [HaSu02]:

The natural density of EHS numbers exists and equals 1.
-/
theorem erdos_problem_1074_part1 :
    Tendsto (fun x : ℕ =>
      (countEHS x : ℝ) / (x : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1074, Part 2 [HaSu02]:

The relative density of Pillai primes among all primes exists and equals 1.
-/
theorem erdos_problem_1074_part2 :
    Tendsto (fun x : ℕ =>
      (countPillaiPrimes x : ℝ) / (primeCount x : ℝ))
      atTop (nhds 1) :=
  sorry

end
