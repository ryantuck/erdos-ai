import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

/--
The set of odd positive integers that cannot be expressed as 2^k + p for any
non-negative integer k and any prime p.
-/
def oddNotPowerOfTwoPlusPrime : Set ℕ :=
  {n : ℕ | Odd n ∧ ∀ (k : ℕ) (q : ℕ), Nat.Prime q → n ≠ 2 ^ k + q}

/--
A set S ⊆ ℕ has natural density zero if |S ∩ {1, ..., N}| / N → 0 as N → ∞.
-/
def HasNaturalDensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun N : ℕ => (Set.ncard (S ∩ Set.Icc 1 N) : ℝ) / (N : ℝ))
    atTop (nhds 0)

/--
A set AP ⊆ ℕ is an infinite arithmetic progression if there exist a, d : ℕ
with d > 0 and AP = {a + m * d | m : ℕ}.
-/
def IsInfiniteAP (AP : Set ℕ) : Prop :=
  ∃ (a d : ℕ), 0 < d ∧ AP = {n : ℕ | ∃ m : ℕ, n = a + m * d}

/--
Erdős Problem #16 [Er95, p.167] (Disproved — Chen 2023):

Erdős asked whether the set of odd integers not of the form 2^k + p (where p
is prime and k ≥ 0) is the union of an infinite arithmetic progression and a
set of natural density 0. He called this conjecture 'rather silly'.

Using covering congruences, Erdős [Er50] proved that this set contains an
infinite arithmetic progression. Chen [Ch23] proved the answer is no: the set
is NOT the union of an infinite arithmetic progression and a density-0 set.

Formally: there do not exist sets AP and D such that AP is an infinite
arithmetic progression, D has natural density 0, and the set of odd integers
not of the form 2^k + p equals AP ∪ D.
-/
theorem erdos_problem_16 :
    ¬ ∃ (AP D : Set ℕ),
        IsInfiniteAP AP ∧
        HasNaturalDensityZero D ∧
        oddNotPowerOfTwoPlusPrime = AP ∪ D :=
  sorry
