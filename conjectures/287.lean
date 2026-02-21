import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs

/-!
# Erdős Problem #287

Let k ≥ 2. Is it true that, for any distinct integers 1 < n₁ < ⋯ < nₖ such that
1 = 1/n₁ + ⋯ + 1/nₖ, we must have max(nᵢ₊₁ - nᵢ) ≥ 3?

The example 1 = 1/2 + 1/3 + 1/6 shows that 3 would be best possible here.
The lower bound of ≥ 2 is equivalent to saying that 1 is not the sum of
reciprocals of consecutive integers, proved by Erdős [Er32].
-/

/--
Erdős Problem #287 [ErGr80,p.33]:

For any finite set S of natural numbers with |S| ≥ 2, all elements > 1,
whose reciprocals sum to 1, the maximum gap between consecutive elements
of S (in sorted order) is at least 3. That is, there exist consecutive
elements a, b in S with b - a ≥ 3.
-/
theorem erdos_problem_287 :
    ∀ (S : Finset ℕ),
      2 ≤ S.card →
      (∀ n ∈ S, 1 < n) →
      S.sum (fun n => (1 : ℚ) / ↑n) = 1 →
      ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ c ∈ S, c ≤ a ∨ b ≤ c) ∧ 3 ≤ b - a :=
  sorry
