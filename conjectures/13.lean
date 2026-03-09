import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Erdős Problem #13

Let A ⊆ {1,...,N} be such that there are no a, b, c ∈ A with a ∣ (b + c)
and a < min(b, c). Is it true that |A| ≤ N/3 + O(1)?

Asked by Erdős and Sárközy. The answer is yes, proved by Bedert [Be23].
-/

/-- A set A ⊆ {1,...,N} is *sum-divisibility-free* if there are no
    a, b, c ∈ A with a ∣ (b + c) and a < min(b, c). -/
def IsSumDivFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ∣ (b + c) → a < min b c → False

/--
Erdős Problem #13 [Er73, Er75b, Er77c, Er92c, Er95c, Er97, Er97b, Er97e, Er98]:
Let A ⊆ {1,...,N} be sum-divisibility-free. Then |A| ≤ N/3 + C for some
absolute constant C.

Proved by Bedert [Be23].
-/
theorem erdos_problem_13 :
    ∃ C : ℝ, ∀ N : ℕ, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      IsSumDivFree A →
      (A.card : ℝ) ≤ (N : ℝ) / 3 + C :=
  sorry
