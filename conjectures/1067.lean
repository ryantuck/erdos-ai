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
    distinct vertices and every n : ℕ, there exist n paths between them with
    pairwise disjoint internal vertices. -/
def SimpleGraph.IsInfinitelyConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ u v : V, u ≠ v →
    ∀ n : ℕ, ∃ (paths : Fin n → G.Walk u v),
      (∀ i, (paths i).IsPath) ∧
      ∀ i j : Fin n, i ≠ j →
        Disjoint (paths i).internalVertices (paths j).internalVertices

/--
Erdős Problem #1067 [ErHa66,p.77][ErHa85]:

Does every graph with chromatic number ℵ₁ contain an infinitely connected
subgraph with chromatic number ℵ₁?

A question of Erdős and Hajnal. A graph is infinitely connected if any two
vertices are connected by infinitely many pairwise (internally) vertex-disjoint
paths.

Disproved by Soukup [So15], who constructed a counterexample in ZFC.
A simpler example was given by Bowler and Pitz [BoPi24].
-/
theorem erdos_problem_1067 :
    ¬ (∀ (V : Type) (G : SimpleGraph V),
      ¬G.CardColorable ℵ₀ →
      ∃ (S : Set V),
        (G.induce S).IsInfinitelyConnected ∧
        ¬(G.induce S).CardColorable ℵ₀) :=
  sorry
