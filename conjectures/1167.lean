import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Finset.Basic

open Cardinal

noncomputable section

/-!
# Erdős Problem #1167

Let r ≥ 2 be finite and λ be an infinite cardinal. Let κ_α be cardinals for
all α < γ.

Is it true that 2^λ → (κ_α + 1)_{α < γ}^{r+1} implies λ → (κ_α)_{α < γ}^r?

Here + means cardinal addition, so κ_α + 1 = κ_α if κ_α is infinite.

A problem of Erdős, Hajnal, and Rado.

Tags: set theory, ramsey theory
-/

/-- The cardinal partition relation κ → (targets α)_{α : ι}^r:
    for every coloring of the r-element subsets of a κ-sized set with colors from ι,
    there exists a color i and a monochromatic subset of cardinality ≥ targets i. -/
def CardinalPartitionRel (κ : Cardinal) {ι : Type*} (targets : ι → Cardinal) (r : ℕ) : Prop :=
  ∀ (S : Type*) [DecidableEq S] (_ : #S = κ) (c : Finset S → ι),
    ∃ (i : ι) (H : Set S),
      Cardinal.mk H ≥ targets i ∧
      ∀ s : Finset S, s.card = r → (↑s : Set S) ⊆ H → c s = i

/-- **Erdős Problem #1167** (Erdős–Hajnal–Rado):
    For r ≥ 2 and λ infinite, does 2^λ → (κ_α + 1)^{r+1} imply λ → (κ_α)^r? -/
theorem erdos_conjecture_1167
    {ι : Type*} (κ : ι → Cardinal) (lam : Cardinal) (r : ℕ)
    (hr : r ≥ 2) (hlam : ℵ₀ ≤ lam) :
    CardinalPartitionRel ((2 : Cardinal) ^ lam) (fun α => κ α + 1) (r + 1) →
    CardinalPartitionRel lam κ r :=
  sorry

end
