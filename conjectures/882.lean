import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #882

What is the size of the largest A ⊆ {1, …, n} such that the set of all
non-empty subset sums { ∑_{a ∈ S} a : ∅ ≠ S ⊆ A } is primitive (no two
distinct elements divide each other)?

A problem of Erdős and Sárkőzy [Er98]. The greedy algorithm shows
|A| ≥ (1 - o(1)) log₃ n. Erdős, Lev, Rauzy, Sándor, and Sárközy [ELRSS99]
proved |A| > log₂ n − 1 is achievable. The upper bound
|A| ≤ log₂ n + ½ log₂ log n + O(1) follows from the distinct subset sums
property. It is conjectured that |A| ≤ log₂ n + O(1).

https://www.erdosproblems.com/882

Tags: number theory, primitive sets
-/

/-- The set of all non-empty subset sums of a finset A of natural numbers. -/
def subsetSums882 (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (fun S => S.sum id)

/-- A finset of natural numbers is *primitive* if no element divides another
    distinct element. -/
def IsPrimitive882 (B : Finset ℕ) : Prop :=
  ∀ a ∈ B, ∀ b ∈ B, a ∣ b → a = b

/-- The maximum size of A ⊆ {1, …, n} whose non-empty subset sums form a
    primitive set. -/
noncomputable def maxPrimitiveSubsetSumSize882 (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ A.card = k ∧
    IsPrimitive882 (subsetSums882 A)}

/--
Erdős Problem #882, lower bound [ELRSS99]:

For all sufficiently large n, there exists A ⊆ {1, …, n} with
|A| > log₂ n − 1 such that the non-empty subset sums of A form a primitive set.

The construction is A = {2^m − 2^{m−1}, 2^m − 2^{m−2}, …, 2^m − 1}.
-/
theorem erdos_problem_882_lower :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (maxPrimitiveSubsetSumSize882 n : ℝ) > Real.log n / Real.log 2 - 1 :=
  sorry

/--
Erdős Problem #882, conjectured upper bound:

There exists a constant C such that for all sufficiently large n,
the maximum size of A ⊆ {1, …, n} whose non-empty subset sums are
primitive satisfies |A| ≤ log₂ n + C.
-/
theorem erdos_problem_882_upper :
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (maxPrimitiveSubsetSumSize882 n : ℝ) ≤ Real.log n / Real.log 2 + C :=
  sorry

end
