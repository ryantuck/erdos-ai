import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

namespace Erdos1097

/--
The set of common differences of three-term arithmetic progressions in `A`.
That is, `d` is in this set if there exists `a ∈ A` with `a + d ∈ A` and `a + 2 * d ∈ A`.
-/
noncomputable def apDiffs (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.2 - p.1) |>.filter (fun d =>
    ∃ a ∈ A, a + d ∈ A ∧ a + 2 * d ∈ A)

/-- Erdős Problem #1097 (OPEN) [GWNT89]:

Let A be a set of n integers. How many distinct d can occur as the common
difference of a three-term arithmetic progression in A? Are there always
O(n^{3/2}) many such d?

Erdős and Spencer gave a probabilistic proof that there exist sets achieving
n^{3/2} such differences. The conjecture is that this is the best possible.
-/
theorem erdos_problem_1097 :
    ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
      ((apDiffs A).card : ℝ) ≤ C * (A.card : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry

end Erdos1097
