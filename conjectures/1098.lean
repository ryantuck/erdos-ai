import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Finite.Defs

noncomputable section

open SimpleGraph

/-- The non-commuting graph of a group G has vertices the elements of G,
    with an edge between g and h if and only if they do not commute (gh ≠ hg). -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm := by intro _ _ hab; exact Ne.symm hab
  loopless := ⟨by intro a hab; exact hab rfl⟩

/--
Erdős Problem #1098 (Proved by Neumann [Ne76]):
Let G be a group and Γ(G) be the non-commuting graph, with vertices the elements
of G and an edge between g and h if and only if gh ≠ hg. If Γ contains no
infinite complete subgraph (i.e., no infinite set of pairwise non-commuting
elements), then there is a finite bound on the size of complete subgraphs of Γ.

Neumann proved that Γ contains no infinite complete subgraph if and only if
the centre of G has finite index, and if the centre has index n then Γ
contains no complete subgraph on more than n vertices.
-/
theorem erdos_problem_1098 (G : Type*) [Group G] :
    (¬ ∃ S : Set G, S.Infinite ∧ (nonCommutingGraph G).IsClique S) →
    (∃ n : ℕ, ∀ S : Finset G, (nonCommutingGraph G).IsClique (S : Set G) → S.card ≤ n) :=
  sorry

end
