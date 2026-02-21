import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #548

Let n ≥ k+1. Every graph on n vertices with at least (k-1)/2 · n + 1 edges
contains every tree on k+1 vertices.

This is the Erdős–Sós conjecture [Er64c][Er74c][Er93].
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/--
Erdős Problem #548 [Er64c][Er74c,p.78][Er93,p.345]:

Let n ≥ k+1. Every graph on n vertices with at least (k-1)/2 · n + 1 edges
contains every tree on k+1 vertices.

The edge condition is expressed as 2 · |E(G)| ≥ (k-1) · n + 2 to avoid
division in the naturals.
-/
theorem erdos_problem_548 (k n : ℕ) (hn : n ≥ k + 1)
    (G : SimpleGraph (Fin n))
    (hE : 2 * G.edgeSet.ncard ≥ (k - 1) * n + 2)
    (T : SimpleGraph (Fin (k + 1))) (hT : T.IsTree) :
    ContainsSubgraphCopy T G :=
  sorry

end
