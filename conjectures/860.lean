import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

noncomputable section

open Filter

/-!
# Erdős Problem #860

Let h(n) be such that, for any m ≥ 1, in the interval (m, m + h(n)) there
exist distinct integers aᵢ for 1 ≤ i ≤ π(n) such that pᵢ ∣ aᵢ, where pᵢ
denotes the i-th prime.

Estimate h(n).

A problem of Erdős and Pomerance [ErPo80], who proved that
  h(n) ≪ n^{3/2} / (log n)^{1/2}.
Erdős and Selfridge proved h(n) > (3 - o(1))n, and Ruzsa proved h(n)/n → ∞.
-/

/-- A prime covering of (m, m + h) for primes up to n: an injective assignment
    of distinct integers in (m, m + h), one for each prime p ≤ n, such that
    p divides the integer assigned to it. -/
def HasPrimeCovering (n m h : ℕ) : Prop :=
  ∃ a : {p : ℕ // p.Prime ∧ p ≤ n} → ℕ,
    Function.Injective a ∧
    (∀ p, m < a p ∧ a p < m + h) ∧
    (∀ p, p.val ∣ a p)

/-- `erdosPomeranceH n` is the smallest h such that for every m ≥ 1,
    in the open interval (m, m + h) one can find π(n) distinct multiples,
    one for each prime p ≤ n. -/
noncomputable def erdosPomeranceH (n : ℕ) : ℕ :=
  sInf {h : ℕ | ∀ m : ℕ, m ≥ 1 → HasPrimeCovering n m h}

/--
Erdős Problem #860, upper bound (Erdős–Pomerance [ErPo80]):

There exists C > 0 such that for all sufficiently large n,
  h(n) ≤ C · n^{3/2} / (log n)^{1/2}.
-/
theorem erdos_problem_860_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdosPomeranceH n : ℝ) ≤
        C * (n : ℝ) ^ ((3 : ℝ) / 2) / (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #860, lower bound (Ruzsa):
  h(n) / n → ∞ as n → ∞.
-/
theorem erdos_problem_860_lower_ruzsa :
    Tendsto (fun n => (erdosPomeranceH n : ℝ) / (n : ℝ)) atTop atTop :=
  sorry

end
