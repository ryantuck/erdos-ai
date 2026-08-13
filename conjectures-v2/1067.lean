import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.SetTheory.Cardinal.Aleph

open Cardinal SimpleGraph

universe u

/-- A graph is properly colorable with at most κ colors (cardinal-valued). -/
def SimpleGraph.CardColorable {V : Type u} (G : SimpleGraph V) (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u), #α ≤ κ ∧ Nonempty (G.Coloring α)

/-- The internal vertices of a walk from u to v: all vertices on the walk
    other than the two endpoints. -/
def SimpleGraph.Walk.internalVertices {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) : Set V :=
  {w | w ∈ p.support ∧ w ≠ u ∧ w ≠ v}

/-- A graph is infinitely connected if it is connected and for every pair of
    distinct vertices and every n : ℕ, there exist n pairwise distinct paths
    between them with pairwise disjoint internal vertices.

    The distinctness requirement is essential: the single-edge path between
    adjacent vertices has an empty internal vertex set, so without it n copies
    of that one path would vacuously satisfy pairwise internal disjointness,
    and any complete graph (even K₂) would count as infinitely connected.
    With distinctness, at most one path in a disjoint family can have empty
    internal vertex set (the edge path is the unique such path), so this
    captures the intended notion. Since paths are finite, having n pairwise
    internally disjoint distinct paths for every n is equivalent to having an
    infinite pairwise internally disjoint family (a maximal disjoint family
    that is finite would bound all disjoint families via its finite set of
    internal vertices). -/
def SimpleGraph.IsInfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ u v : V, u ≠ v →
    ∀ n : ℕ, ∃ (paths : Fin n → G.Walk u v),
      (∀ i, (paths i).IsPath) ∧
      ∀ i j : Fin n, i ≠ j →
        paths i ≠ paths j ∧
        Disjoint (paths i).internalVertices (paths j).internalVertices

/-- A graph is infinitely edge-connected if removing any finite set of edges
    leaves the graph connected: the graph is nonempty and, for every finite
    set s of edges, any two vertices are joined by a walk using no edge of s.
    (This is `(G.deleteEdges s).Connected` unfolded, stated via walks so as to
    use only the constructs already imported in this file.) -/
def SimpleGraph.IsInfinitelyEdgeConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty V ∧
  ∀ s : Set (Sym2 V), s.Finite →
    ∀ u v : V, ∃ p : G.Walk u v, ∀ e ∈ p.edges, e ∉ s

/--
Erdős Problem #1067 [ErHa66,p.77][ErHa85]:

Does every graph with chromatic number $\aleph_1$ contain an infinitely connected
subgraph with chromatic number $\aleph_1$?

A question of Erdős and Hajnal. A graph is infinitely connected if any two
vertices are connected by infinitely many pairwise (internally) vertex-disjoint
paths.

Komjáth [Ko13] proved that it is consistent that the answer is no. This was
improved by Soukup [So15], who constructed a counterexample using no extra
set-theoretical assumptions (i.e. in ZFC). A simpler elementary example was
given by Bowler and Pitz [BoPi24]. The problem is listed as DISPROVED (LEAN)
on erdosproblems.com: the negative solution has been verified in Lean
(formalized by Alexeev using Aristotle and Aleph Prover;
https://github.com/plby/lean-proofs/blob/main/src/v4.24.0/ErdosProblems/Erdos1067.lean).

In [ErHa66] Erdős and Hajnal asked the same question under the additional
assumption that the graph has $\aleph_1$ many vertices; Komjáth [Ko13] proved
that this version is independent of ZFC (not formalized here, since
independence results are not directly expressible as a single Lean statement).
See also Problem #1068.

Formalization notes:
* "chromatic number $\aleph_1$" is rendered as
  `CardColorable (ℵ_ 1) ∧ ¬ CardColorable ℵ₀`, which says the chromatic
  number is exactly $\aleph_1$ (colorable with $\aleph_1$ colors but not with
  countably many; since no cardinal lies strictly between $\aleph_0$ and
  $\aleph_1$, this pins the least admissible number of colors to $\aleph_1$).
* "subgraph" is rendered as an induced subgraph `G.induce S`. This is
  equivalent to allowing arbitrary subgraphs: passing from a subgraph to the
  induced graph on the same vertex set only adds edges, which preserves
  infinite connectivity and cannot decrease the chromatic number.
* Since the answer is "no", the statement asserts the negation of the
  universally quantified question.

References:
[ErHa66] Erdős, P. and Hajnal, A., On chromatic number of graphs and
set-systems. Acta Math. Acad. Sci. Hungar. 17 (1966), 61–99.
[ErHa85] Erdős, P. and Hajnal, A. (1985). [bibliographic details not
recovered; stub]
[Ko13] Komjáth, Péter, A note on chromatic number and connectivity of
infinite graphs. Israel J. Math. (2013), 499–506.
[So15] Soukup, Dániel T., Trees, ladders and graphs. J. Combin. Theory
Ser. B (2015), 96–116.
[Th17] Thomassen, Carsten, Infinitely connected subgraphs in graphs of
uncountable chromatic number. Combinatorica (2017), 785–793.
[BoPi24] Bowler, N. and Pitz, M., A note on uncountably chromatic graphs.
arXiv:2402.05984 (2024).
-/
theorem erdos_problem_1067 :
    ¬ (∀ (V : Type) (G : SimpleGraph V),
      G.CardColorable (ℵ_ 1) → ¬G.CardColorable ℵ₀ →
      ∃ (S : Set V),
        (G.induce S).IsInfinitelyConnected ∧
        (G.induce S).CardColorable (ℵ_ 1) ∧ ¬(G.induce S).CardColorable ℵ₀) :=
  sorry

/--
Variant (Thomassen [Th17]): the analogous question for infinite
edge-connectivity — must every graph with chromatic number $\aleph_1$ contain
an infinitely edge-connected subgraph with chromatic number $\aleph_1$? —
also has a negative answer: Thomassen constructed a counterexample to the
version which asks for infinite edge-connectivity (that is, to disconnect the
graph requires deleting infinitely many edges).
-/
theorem erdos_problem_1067.variants.infinite_edge_connectivity :
    ¬ (∀ (V : Type) (G : SimpleGraph V),
      G.CardColorable (ℵ_ 1) → ¬G.CardColorable ℵ₀ →
      ∃ (S : Set V),
        (G.induce S).IsInfinitelyEdgeConnected ∧
        (G.induce S).CardColorable (ℵ_ 1) ∧ ¬(G.induce S).CardColorable ℵ₀) :=
  sorry
