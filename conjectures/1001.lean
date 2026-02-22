import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open MeasureTheory Set Filter

noncomputable section

/-!
# Erdős Problem #1001

Let S(N, A, c) be the Lebesgue measure of the set of α ∈ (0,1) such that
  |α - x/y| < A/y²
for some N ≤ y ≤ cN and gcd(x,y) = 1. Does
  lim_{N → ∞} S(N, A, c) = f(A, c)
exist? What is its explicit form?

A problem of Erdős, Szüsz, and Turán [EST58], who proved the formula
  f(A, c) = 12A log c / π²
when 0 < A < c/(1 + c²).

The existence of the limit was proved by Kesten and Sós [KeSo66].
Alternative, more explicit proofs were given by Boca [Bo08] and
Xiong–Zaharescu [XiZa06].
-/

/-- The set of α ∈ (0,1) approximable by a coprime fraction x/y
    with N ≤ y ≤ cN to within A/y². -/
def approxSet (N : ℕ) (A c : ℝ) : Set ℝ :=
  {α : ℝ | α ∈ Ioo 0 1 ∧
    ∃ (x : ℤ) (y : ℕ), N ≤ y ∧ (y : ℝ) ≤ c * N ∧
      Nat.Coprime (Int.natAbs x) y ∧
      |α - (x : ℝ) / (y : ℝ)| < A / ((y : ℝ) ^ 2)}

/-- S(N, A, c) is the Lebesgue measure of the approximation set. -/
def S_measure (N : ℕ) (A c : ℝ) : ℝ :=
  (volume (approxSet N A c)).toReal

/--
Erdős Problem #1001 [Er64b]:

For all A > 0 and c > 1, the limit lim_{N → ∞} S(N, A, c) exists.

Proved by Kesten and Sós [KeSo66].
-/
theorem erdos_problem_1001 (A c : ℝ) (hA : 0 < A) (hc : 1 < c) :
    ∃ L : ℝ, Tendsto (fun N : ℕ => S_measure N A c) atTop (nhds L) :=
  sorry

end
