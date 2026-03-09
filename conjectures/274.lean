import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
open Subgroup
open scoped Pointwise

/--
Erdős Problem #274 [Er77c, ErGr80, Er97c] (Herzog-Schönheim Conjecture):

If G is a group and a₁G₁, …, aₖGₖ are finitely many left cosets of subgroups
G₁, …, Gₖ of G with distinct indices [G : Gᵢ], then the cosets a₁G₁, …, aₖGₖ
cannot form a partition of G. Equivalently, there is no exact covering of G by
cosets of subgroups all having different indices.

This was proved when all Gᵢ are subnormal in G by Sun (2004), which in
particular settles the abelian case asked about by Erdős.
-/
theorem erdos_problem_274 (G : Type*) [Group G] :
    ∀ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → G),
      -- All indices are finite and pairwise distinct
      (∀ i, (H i).index ≠ 0) →
      (∀ i j, i ≠ j → (H i).index ≠ (H j).index) →
      -- k ≥ 2 (more than one coset)
      k ≥ 2 →
      -- Then the left cosets do not partition G
      ¬(∀ g : G, ∃! i : Fin k, g ∈ (a i) • (H i : Set G)) :=
  sorry
