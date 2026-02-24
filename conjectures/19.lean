import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #19 (Erdős–Faber–Lovász Conjecture)

If G is an edge-disjoint union of n copies of K_n, then χ(G) = n.

Conjectured by Erdős, Faber, and Lovász in 1972. Proved for all sufficiently
large n by Kang, Kelly, Kühn, Methuku, and Osthus [KKKMO21]. The problem is
DECIDABLE (resolved up to a finite check).

Tags: graph theory, chromatic number
https://www.erdosproblems.com/19
-/

/--
**Erdős–Faber–Lovász Conjecture (Erdős Problem #19)**:

If G is an edge-disjoint union of n copies of K_n, then χ(G) = n.

We formalize "G is an edge-disjoint union of n copies of K_n" as: there
exist n cliques (vertex sets), each of size n, such that
- each clique is a complete subgraph of G (an n-clique),
- any two distinct cliques share at most one vertex (equivalently, they are
  edge-disjoint, since two shared vertices would force a shared edge), and
- every edge of G lies in some clique.
-/
theorem erdos_problem_19 (n : ℕ) (hn : 2 ≤ n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cliques : Fin n → Finset V)
    -- Each clique is a copy of K_n in G
    (hclique : ∀ i : Fin n, G.IsNClique n (cliques i))
    -- Any two distinct cliques share at most one vertex (edge-disjointness)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ((cliques i) ∩ (cliques j)).card ≤ 1)
    -- Every edge of G lies in some clique
    (hcover : ∀ u v : V, G.Adj u v → ∃ i : Fin n, u ∈ cliques i ∧ v ∈ cliques i) :
    G.chromaticNumber = n :=
  sorry

end
