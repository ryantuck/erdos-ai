import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Finset Filter

/--
An integer m is a **consecutive sum** of the first `bound` terms of a sequence a
if there exist u ≤ v < bound such that m = ∑_{i=u}^{v} a(i).
-/
def IsConsecutiveSum (a : ℕ → ℕ) (bound : ℕ) (m : ℕ) : Prop :=
  ∃ u v : ℕ, u ≤ v ∧ v < bound ∧ ∑ i ∈ Icc u v, a i = m

/--
A sequence a : ℕ → ℕ is a **MacMahon sequence** starting from n if:
1. a(0) = n, and
2. For each i, a(i+1) is the least positive integer not representable as a sum
   of consecutive terms a(u), a(u+1), …, a(v) for any u ≤ v ≤ i.

This means: a(i+1) is not itself a consecutive sum of the first i+1 terms,
and every positive integer less than a(i+1) is such a consecutive sum.
-/
def IsMacMahonSeq (a : ℕ → ℕ) (n : ℕ) : Prop :=
  a 0 = n ∧
  ∀ i : ℕ,
    1 ≤ a (i + 1) ∧
    ¬ IsConsecutiveSum a (i + 1) (a (i + 1)) ∧
    ∀ m : ℕ, 1 ≤ m → m < a (i + 1) → IsConsecutiveSum a (i + 1) m

/--
Erdős Problem #359 [Er77c, Er78f, ErGr80]:

Let a₁ < a₂ < ⋯ be an infinite sequence of integers such that a₁ = n and
a_{i+1} is the least integer which is not a sum of consecutive earlier aⱼs.

In the case n = 1, can one prove that aₖ/k → ∞ and aₖ/k^{1+c} → 0 for
any c > 0?

A problem of MacMahon, studied by Andrews. When n = 1 this sequence begins
1, 2, 4, 5, 8, 10, 14, 15, … (OEIS A002048). Andrews conjectures
aₖ ~ k log k / log log k.
-/
theorem erdos_problem_359 (a : ℕ → ℕ) (ha : IsMacMahonSeq a 1) :
    Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ)) atTop atTop ∧
    ∀ c : ℝ, 0 < c →
      Tendsto (fun k : ℕ => (a k : ℝ) / (k : ℝ) ^ (1 + c)) atTop (nhds 0) :=
  sorry
