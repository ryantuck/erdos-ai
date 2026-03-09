import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

noncomputable section

/--
The multiset of k-element subset sums of a finite set A ⊆ ℂ.
For each k-element subset of A, we take the sum of its elements.
-/
def subsetSumMultiset (A : Finset ℂ) (k : ℕ) : Multiset ℂ :=
  (A.powersetCard k).val.map (fun s => s.sum id)

/--
Erdős Problem #494 [Er61]:

If A ⊂ ℂ is a finite set and k ≥ 1, let
  A_k = { z₁ + ⋯ + zₖ : zᵢ ∈ A distinct }
(as a multiset). For k > 2, does the multiset A_k (together with |A|)
uniquely determine A?

This is false for small |A| (e.g. |A| = k or |A| = 2k), but
Gordon, Fraenkel, and Straus proved that for all k, the multiset A_k
uniquely determines A provided |A| is sufficiently large.
-/
theorem erdos_problem_494 (k : ℕ) (hk : k > 2) :
    ∃ N : ℕ, ∀ (A B : Finset ℂ),
      A.card > N → A.card = B.card →
      subsetSumMultiset A k = subsetSumMultiset B k →
      A = B :=
  sorry

end
