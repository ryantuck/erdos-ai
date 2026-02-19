import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

/--
Erdős-Faber-Lovász Conjecture (Problem #19):
If G is an edge-disjoint union of n copies of K_n, then χ(G) = n.

We model the "union of n copies of K_n" by taking n sets of vertices (the vertices of each K_n),
each of size n, such that the intersection of any two sets has size at most 1 (edge-disjointness).
The graph G is then the graph on the union of these vertices where two vertices are adjacent
if they belong to the same set.
-/
theorem erdos_faber_lovasz_conjecture (n : ℕ) {V : Type*} [DecidableEq V]
    (C : Fin n → Finset V)
    (h_card : ∀ i, (C i).card = n)
    (h_inter : ∀ i j, i ≠ j → (C i ∩ C j).card ≤ 1) :
    let G : SimpleGraph V := {
      Adj := λ u v ↦ u ≠ v ∧ ∃ i, u ∈ C i ∧ v ∈ C i,
      symm := by
        intros u v h
        rcases h with ⟨hne, i, hui, hvi⟩
        exact ⟨hne.symm, i, hvi, hui⟩,
      loopless := ⟨by
        intros v h
        exact h.1 rfl⟩
    }
    G.chromaticNumber = n :=
sorry
