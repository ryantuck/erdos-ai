import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1074

Let S be the set of all m ≥ 1 such that there exists a prime p ≢ 1 (mod m)
with p ∣ m! + 1. Such m are called "EHS numbers" (after Erdős, Hardy, and
Subbarao). The sequence begins 8, 9, 13, 14, 15, 16, 17, … (OEIS A064164).

Let P be the set of all primes p such that there exists an m with
p ≢ 1 (mod m) and p ∣ m! + 1. Such primes are called "Pillai primes".
The sequence begins 23, 29, 59, 61, 67, 71, … (OEIS A063980).

**Part (a):** Does the asymptotic density of S exist, and is it equal to 1?

**Part (b):** Does the relative density of P among the primes exist, and is
it equal to 1?

Reference: [HaSu02], [Gu04] (problem A2 in Guy's collection).
https://www.erdosproblems.com/1074
-/

/-- An "EHS number": m ≥ 1 such that some prime p ≢ 1 (mod m) divides m! + 1. -/
def IsEHSNumber (m : ℕ) : Prop :=
  1 ≤ m ∧ ∃ p : ℕ, Nat.Prime p ∧ p ∣ (m.factorial + 1) ∧ ¬(p % m = 1 % m)

/-- A "Pillai prime": a prime p such that some m has p ∣ m! + 1 and p ≢ 1 (mod m). -/
def IsPillaiPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ ∃ m : ℕ, p ∣ (m.factorial + 1) ∧ ¬(p % m = 1 % m)

/-- Count of EHS numbers in [1, N]. -/
noncomputable def ehsCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun m => IsEHSNumber m)).card

/-- Count of Pillai primes in [1, N]. -/
noncomputable def pillaiPrimeCount (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => IsPillaiPrime p)).card

/-- Count of all primes in [1, N]. -/
noncomputable def primeCount1074 (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun p => Nat.Prime p)).card

/--
Erdős Problem #1074, Part (a) [HaSu02]:

The asymptotic density of EHS numbers exists and equals 1.
That is, |S ∩ [1, N]| / N → 1 as N → ∞.
-/
theorem erdos_problem_1074a :
    Filter.Tendsto
      (fun N : ℕ => (ehsCount N : ℝ) / (N : ℝ))
      atTop (nhds 1) :=
  sorry

/--
Erdős Problem #1074, Part (b) [HaSu02]:

The relative density of Pillai primes among all primes exists and equals 1.
That is, |P ∩ [1, N]| / π(N) → 1 as N → ∞.
-/
theorem erdos_problem_1074b :
    Filter.Tendsto
      (fun N : ℕ => (pillaiPrimeCount N : ℝ) / (primeCount1074 N : ℝ))
      atTop (nhds 1) :=
  sorry

end
