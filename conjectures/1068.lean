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

/-- A graph is infinitely (vertex) connected if it is infinite, connected, and any two
    distinct vertices are joined by an infinite set of paths whose internal vertex sets
    are pairwise disjoint.  Using an infinite *set* of paths makes the paths genuinely
    distinct, matching "infinitely many pairwise vertex-disjoint paths" literally.

    The `Infinite V` conjunct reflects the standard convention that an infinitely
    connected graph is k-connected for every k, hence infinite.  Without it, a
    one-vertex graph would satisfy the pair condition vacuously (and with a
    `Fin n`-indexed family in place of a set, so would any single edge, via the
    constant family of the edge path, whose internal vertex set is empty); either
    degeneracy would make the statement of erdos_problem_1068 trivially true. -/
def SimpleGraph.IsInfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  Infinite V ∧ G.Connected ∧
  ∀ u v : V, u ≠ v →
    ∃ (P : Set (G.Walk u v)), P.Infinite ∧ (∀ p ∈ P, p.IsPath) ∧
      P.Pairwise (fun p q => Disjoint p.internalVertices q.internalVertices)

/--
Erdős Problem #1068 [Va99,7.90] (OPEN):

Does every graph with chromatic number ℵ₁ contain a countable subgraph which
is infinitely vertex-connected?

A graph is infinitely (vertex) connected if any two vertices are connected by
infinitely many pairwise (internally) vertex-disjoint paths.

"Chromatic number ℵ₁" is encoded exactly: G is properly colorable with ℵ₁
colors but not with countably many.  Stated as a direct assertion of the "yes"
direction of the open question (raw-file style); the upstream formalization in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1068.lean)
states it as `answer(sorry) ↔ ...` with `chromaticCardinal = ℵ_1`.

This is described in [BoPi24] as a 'version of the Erdős-Hajnal problem' (which
is problem #1067), but it does not seem to appear in [ErHa66].  Soukup [So15]
constructed a graph with uncountable chromatic number in which every uncountable
set is finitely vertex-connected; a simpler construction was given by Bowler and
Pitz [BoPi24].  See also problem #1067.

References (stubs; journal volumes partly unrecoverable offline):
[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999), §7.90.
[ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and
  set-systems_. Acta Math. Acad. Sci. Hungar. **17** (1966), 61-99.
[So15] Soukup, D. T., _Trees, ladders and graphs_. J. Combin. Theory Ser. B
  (2015), 96-116.
[BoPi24] Bowler, N. and Pitz, M., _A note on uncountably chromatic graphs_.
  arXiv:2402.05984 (2024).

Source: erdosproblems.com/1068 (page edition 23 January 2026, accessed
2026-03-06).
-/
theorem erdos_problem_1068 :
    ∀ (V : Type) (G : SimpleGraph V),
      ¬G.CardColorable ℵ₀ →
      G.CardColorable (aleph 1) →
      ∃ (S : Set V),
        Set.Countable S ∧
        (G.induce S).IsInfinitelyConnected :=
  sorry

/--
Soukup [So15] constructed a graph with uncountable chromatic number in which
every uncountable set of vertices is finitely vertex-connected, i.e. induces a
subgraph that is not infinitely connected.  A simpler construction was given by
Bowler and Pitz [BoPi24].  Hence the analogue of problem #1068 for *uncountable*
subgraphs fails.  (For uncountable S the `Infinite` conjunct of
`IsInfinitelyConnected` holds automatically, so its negation says the induced
subgraph is disconnected or some pair of vertices has no infinite family of
pairwise internally vertex-disjoint paths.)
-/
theorem erdos_problem_1068.variants.soukup :
    ∃ (V : Type) (G : SimpleGraph V),
      ¬G.CardColorable ℵ₀ ∧
      ∀ (S : Set V), ¬S.Countable → ¬(G.induce S).IsInfinitelyConnected :=
  sorry
