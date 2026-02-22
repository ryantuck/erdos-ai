import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.SetTheory.Cardinal.Ordinal

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #1068

Does every graph with chromatic number ℵ₁ contain a countable subgraph which
is infinitely vertex-connected?

Here "infinitely (vertex) connected" means any two vertices are connected by
infinitely many pairwise vertex-disjoint paths.

https://www.erdosproblems.com/1068
-/

/-- Two walks from u to v are internally vertex-disjoint if every vertex
    appearing in both walks is an endpoint. -/
def SimpleGraph.Walk.InternallyVertexDisjoint {V : Type*} {G : SimpleGraph V}
    {u v : V} (p q : G.Walk u v) : Prop :=
  ∀ w, w ∈ p.support → w ∈ q.support → w = u ∨ w = v

/-- A graph is infinitely vertex-connected if for any two distinct vertices,
    there are arbitrarily many pairwise internally-vertex-disjoint paths
    between them. -/
def IsInfinitelyVertexConnected {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∀ n : ℕ,
    ∃ paths : Fin n → G.Walk u v,
      (∀ i, (paths i).IsPath) ∧
      (∀ i j, i ≠ j → (paths i).InternallyVertexDisjoint (paths j))

/--
Erdős Problem #1068 [Va99,7.90]:

Does every graph with chromatic number ℵ₁ contain a countable subgraph which
is infinitely vertex-connected?

The chromatic number ℵ₁ condition means: G cannot be properly colored with
countably many colors, but can be colored with ℵ₁ many colors.
-/
theorem erdos_problem_1068 {V : Type*} (G : SimpleGraph V)
    -- G has chromatic number exactly ℵ₁:
    -- any proper coloring needs ≥ ℵ₁ colors
    (hχ_lower : ∀ (α : Type*), Nonempty (G.Coloring α) → aleph 1 ≤ #α)
    -- and G is ℵ₁-colorable
    (hχ_upper : ∃ (α : Type*), #α ≤ aleph 1 ∧ Nonempty (G.Coloring α)) :
    ∃ s : Set V, s.Countable ∧ IsInfinitelyVertexConnected (G.induce s) :=
  sorry

end
