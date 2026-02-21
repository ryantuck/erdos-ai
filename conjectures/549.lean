import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #549

If T is a tree which is a bipartite graph with k vertices in one class and 2k
vertices in the other class then R(T) = 4k - 1.

This is a special case of a conjecture of Burr [Bu74] (see [547]).

This conjecture is false: Norin, Sun, and Zhao [NSZ16] proved that if T is the
union of two stars on k and 2k vertices with an edge joining their centres,
then R(T) ≥ (4.2 - o(1))k.
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number R(G) for a graph G on Fin m: the minimum N such that
    every graph H on N vertices contains a copy of G or its complement contains
    a copy of G. -/
noncomputable def ramseyNumber {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/--
Erdős Problem #549 [EFRS82]:

If T is a tree which is a bipartite graph with k vertices in one class and 2k
vertices in the other class then R(T) = 4k - 1.

The bipartition condition is expressed via a proper 2-coloring where one color
class has k vertices and the other has 2k vertices.

This conjecture has been disproved by Norin, Sun, and Zhao [NSZ16].
-/
theorem erdos_problem_549 (k : ℕ) (hk : k ≥ 1)
    (T : SimpleGraph (Fin (3 * k)))
    (hT : T.IsTree)
    (hBip : ∃ c : T.Coloring (Fin 2),
      (Finset.univ.filter (fun v => c v = 0)).card = k ∧
      (Finset.univ.filter (fun v => c v = 1)).card = 2 * k) :
    ramseyNumber T = 4 * k - 1 :=
  sorry

end
