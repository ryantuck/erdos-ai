import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat

open Finset BigOperators

/--
Erdős Problem #360: Sum-free partitions

Let f(n) be minimal such that {1, ..., n-1} can be partitioned into f(n) classes
so that n cannot be expressed as a sum of distinct elements from the same class.
How fast does f(n) grow?

Conlon, Fox, and Pham determined the order of growth up to a multiplicative constant:
  f(n) ≍ n^{1/3} · (n/φ(n)) / ((log n)^{1/3} · (log log n)^{2/3})

References: [ErGr80, p.59], [AlEr96], [Vu07], [CFP21]

A coloring c of {1, ..., n-1} into k colors is sum-free for n if n cannot be
expressed as a sum of distinct elements from any single color class. -/
def SumFreeColoring (n k : ℕ) (c : ℕ → Fin k) : Prop :=
  ∀ j : Fin k, ∀ S : Finset ℕ,
    S ⊆ Icc 1 (n - 1) →
    (∀ x ∈ S, c x = j) →
    S.sum id ≠ n

/-- The minimum number of color classes needed so that {1, ..., n-1} can be colored
    into classes where n is not a sum of distinct elements from any single class. -/
noncomputable def minSumFreeClasses (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ c : ℕ → Fin k, SumFreeColoring n k c}

theorem erdos_problem_360 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      let g := (n : ℝ) ^ ((1 : ℝ) / 3) * ((n : ℝ) / (Nat.totient n : ℝ)) /
        (Real.log (n : ℝ) ^ ((1 : ℝ) / 3) *
         Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))
      C₁ * g ≤ (minSumFreeClasses n : ℝ) ∧
      (minSumFreeClasses n : ℝ) ≤ C₂ * g :=
  sorry
