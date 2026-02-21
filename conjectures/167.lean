import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Card

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #167

Tuza's conjecture (1981): If G is a finite simple graph whose maximum number
of pairwise edge-disjoint triangles (the triangle packing number ν(G)) is at
most k, then G can be made triangle-free by removing at most 2k edges (the
triangle covering number τ(G) is at most 2k).

Equivalently: τ(G) ≤ 2 · ν(G) for every finite graph G.

It is trivial that τ(G) ≤ 3 · ν(G). The examples of K₄ and K₅ show that
2k would be best possible. Haxell [Ha99] improved the trivial bound to
(3 - 3/23 + o(1))k. Kahn and Park [KaPa22] proved this for random graphs.
-/

/--
Erdős Conjecture (Problem #167) — Tuza's Conjecture [Er88]:

For any finite simple graph G, if the maximum number of pairwise edge-disjoint
triangles in G is at most k, then G can be made triangle-free by removing at
most 2k edges.

Two triangles (3-cliques) are edge-disjoint iff their vertex sets share at most
one vertex, since in a triangle every pair of vertices forms an edge.

The hypothesis states that every family of pairwise edge-disjoint triangles
has size at most k. The conclusion states that there exists a subgraph H ≤ G
that is triangle-free, obtained by removing at most 2k edges from G.
-/
theorem erdos_problem_167
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ)
    -- Hypothesis: every family of pairwise edge-disjoint triangles has size ≤ k
    (hpack : ∀ (T : Finset (Finset V)),
      (∀ t ∈ T, G.IsNClique 3 t) →
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → (t₁ ∩ t₂).card ≤ 1) →
      T.card ≤ k) :
    -- Conclusion: G can be made triangle-free by removing ≤ 2k edges
    ∃ (H : SimpleGraph V),
      H ≤ G ∧
      H.CliqueFree 3 ∧
      (G.edgeSet \ H.edgeSet).ncard ≤ 2 * k :=
  sorry

end
