import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Set

noncomputable section

/--
An integer n is a **sum of three nonnegative kth powers** if there exist
a, b, c ∈ ℕ such that a^k + b^k + c^k = n.
-/
def IsSumOfThreeKthPowers (k : ℕ) (n : ℕ) : Prop :=
  ∃ a b c : ℕ, a ^ k + b ^ k + c ^ k = n

/--
f_{k,3}(x) is the number of integers ≤ x which are the sum of three
nonnegative kth powers.
-/
def countSumOfThreeKthPowers (k : ℕ) (x : ℕ) : ℕ :=
  Set.ncard {n : ℕ | n ≤ x ∧ IsSumOfThreeKthPowers k n}

/--
Erdős Problem #325 [ErGr80]:

Let k ≥ 3 and f_{k,3}(x) denote the number of integers ≤ x which are the sum
of three nonnegative kth powers. Is it true that f_{k,3}(x) ≫ x^{3/k}?

The stronger form: for each k ≥ 3 there exists C > 0 such that
f_{k,3}(x) ≥ C · x^{3/k} for all sufficiently large x.

Erdős and Mahler (1938) proved the analogous result for sums of two kth powers:
f_{k,2}(x) ≫ x^{2/k}. For k = 3, the best known bound on f_{3,3}(x) is due
to Wooley (2015): f_{3,3}(x) ≫ x^{0.917…}.
-/
theorem erdos_problem_325_strong (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
      (countSumOfThreeKthPowers k x : ℝ) ≥ C * (x : ℝ) ^ ((3 : ℝ) / k) :=
  sorry

/--
Erdős Problem #325 (weak form):

The weaker version asks whether f_{k,3}(x) ≫_ε x^{3/k - ε} for every ε > 0.
-/
theorem erdos_problem_325_weak (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
      (countSumOfThreeKthPowers k x : ℝ) ≥ C * (x : ℝ) ^ ((3 : ℝ) / k - ε) :=
  sorry

end
