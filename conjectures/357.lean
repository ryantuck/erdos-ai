import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open BigOperators Finset

/--
The consecutive sum ∑_{i=u}^{v} a(i) for a sequence `a : ℕ → ℕ`,
computed as ∑ i in Finset.Icc u v, a i.
-/
noncomputable def consecutiveSum (a : ℕ → ℕ) (u v : ℕ) : ℕ :=
  ∑ i ∈ Icc u v, a i

/--
A strictly increasing sequence `a : ℕ → ℕ` of length `k` (indexed 0 to k-1) has
**distinct consecutive sums** if for any two pairs (u₁, v₁) and (u₂, v₂) with
uⱼ ≤ vⱼ < k, equality of ∑_{i=uⱼ}^{vⱼ} a(i) implies (u₁, v₁) = (u₂, v₂).
-/
def DistinctConsecutiveSums (a : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : ℕ,
    u₁ ≤ v₁ → v₁ < k →
    u₂ ≤ v₂ → v₂ < k →
    consecutiveSum a u₁ v₁ = consecutiveSum a u₂ v₂ →
    u₁ = u₂ ∧ v₁ = v₂

/--
Erdős Problem #357 [Er77c, ErGr80]:

Let 1 ≤ a₁ < ⋯ < aₖ ≤ n be integers such that all consecutive sums
∑_{u ≤ i ≤ v} aᵢ are distinct. Let f(n) be the maximal such k.

Is f(n) = o(n)? That is, does f(n)/n → 0 as n → ∞?

Asked by Erdős and Harzheim. Without the monotonicity requirement,
Hegyvári proved that the answer changes: g(n) grows linearly in n.
-/
theorem erdos_problem_357 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ k : ℕ, ∀ a : ℕ → ℕ,
          StrictMono a →
          (∀ i : ℕ, i < k → 1 ≤ a i ∧ a i ≤ n) →
          DistinctConsecutiveSums a k →
          (k : ℝ) < ε * (n : ℝ) :=
  sorry
