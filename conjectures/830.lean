import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Filter

noncomputable section

/--
The sum-of-divisors function σ(n) = ∑_{d | n} d.
-/
def sigma (n : ℕ) : ℕ := (Nat.divisors n).sum id

/--
A pair (a, b) with a ≤ b is **amicable** if σ(a) = σ(b) = a + b.
-/
def IsAmicablePair (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a ≤ b ∧ sigma a = a + b ∧ sigma b = a + b

/--
Erdős Problem #830 (part 1) [Er83]:

Are there infinitely many amicable pairs? Two natural numbers a, b are an
amicable pair if σ(a) = σ(b) = a + b, where σ is the sum-of-divisors function.
For example, 220 and 284 form an amicable pair.
-/
theorem erdos_problem_830a :
    Set.Infinite {p : ℕ × ℕ | IsAmicablePair p.1 p.2} :=
  sorry

/--
The counting function A(x): the number of amicable pairs (a, b) with
1 ≤ a ≤ b ≤ x.
-/
def amicableCount (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x ×ˢ Finset.Icc 1 x).filter
    fun p => p.1 ≤ p.2 ∧ sigma p.1 = p.1 + p.2 ∧ sigma p.2 = p.1 + p.2).card

/--
Erdős Problem #830 (part 2) [Er83]:

If A(x) counts the number of amicable pairs (a, b) with 1 ≤ a ≤ b ≤ x,
then A(x) > x^{1-o(1)}, i.e., for every ε > 0 and all sufficiently large x,
A(x) > x^{1 - ε}.
-/
theorem erdos_problem_830b :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ (x : ℕ) in atTop,
        (x : ℝ) ^ (1 - ε) < (amicableCount x : ℝ) :=
  sorry

end
