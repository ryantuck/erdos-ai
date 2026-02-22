import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter Finset BigOperators

noncomputable section

/-!
# Erdős Problem #874

Let k(N) denote the size of the largest set A ⊆ {1,…,N} such that the sets
  S_r = { a₁ + ⋯ + aᵣ : a₁ < ⋯ < aᵣ ∈ A }
are disjoint for distinct r ≥ 1. Estimate k(N) — in particular, is it true
that k(N) ~ 2N^{1/2}?

Straus [St66] calls such sets admissible and showed
  liminf k(N)/N^{1/2} ≥ 2   and   limsup k(N)/N^{1/2} ≤ 4/√3.
Erdős–Nicolas–Sárközy [ENS91] improved the upper bound to (143/27)^{1/2}.
The conjecture was proved for all large N by Deshouillers and Freiman [DeFr99].

https://www.erdosproblems.com/874
-/

/-- The set of r-fold subset sums of A: all possible values of a₁ + ⋯ + aᵣ
    where a₁, …, aᵣ are r distinct elements of A. -/
def rSubsetSums (A : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (A.powersetCard r).image (fun S => S.sum id)

/-- A set A ⊆ ℕ is *admissible* (in the sense of Straus) if the r-fold subset
    sums S_r are pairwise disjoint for all distinct r₁ ≠ r₂ with r₁, r₂ ≥ 1. -/
def IsAdmissible874 (A : Finset ℕ) : Prop :=
  ∀ r₁ r₂ : ℕ, 1 ≤ r₁ → 1 ≤ r₂ → r₁ ≠ r₂ →
    Disjoint (rSubsetSums A r₁) (rSubsetSums A r₂)

/-- k(N) is the maximum size of an admissible subset of {1,…,N}. -/
noncomputable def kAdmissible (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsAdmissible874 A ∧ A.card = k}

/--
Erdős Problem #874 (proved by Deshouillers–Freiman [DeFr99]):

k(N) ~ 2N^{1/2}, i.e., for every ε > 0 and all sufficiently large N,
  (2 - ε) · N^{1/2} ≤ k(N) ≤ (2 + ε) · N^{1/2}.
-/
theorem erdos_problem_874 :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (2 - ε) * (N : ℝ) ^ ((1 : ℝ) / 2) ≤ (kAdmissible N : ℝ) ∧
        (kAdmissible N : ℝ) ≤ (2 + ε) * (N : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
