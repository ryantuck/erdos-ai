import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Nat.Choose.Basic

open SimpleGraph Finset

noncomputable section

/-!
# Erdős Problem #915

Let G be a graph with 1+n(m-1) vertices and 1+n·C(m,2) edges. Must G
contain two vertices which are connected by m disjoint paths?

A conjecture of Bollobás and Erdős [BoEr62]. It is unclear whether
"disjoint" means edge-disjoint or (internally) vertex-disjoint. The
above construction (n copies of K_m sharing a single vertex) is valid
for either interpretation.

The vertex-disjoint version was disproved by Leonard [Le73] for m = 5
and by Mader [Ma73] for all m ≥ 6. The edge-disjoint version was
confirmed (and strengthened) by Mader [Ma73].

https://www.erdosproblems.com/915

Tags: graph theory
-/

/-- Two vertices u, v in a simple graph G are connected by m internally
    vertex-disjoint paths if there exist m paths from u to v such that
    no internal vertex of one path appears as an internal vertex of another. -/
def HasInternallyDisjointPaths {V : Type*} (G : SimpleGraph V)
    (u v : V) (m : ℕ) : Prop :=
  ∃ (paths : Fin m → G.Walk u v),
    (∀ i, (paths i).IsPath) ∧
    (∀ i j, i ≠ j → ∀ w : V, w ≠ u → w ≠ v →
      w ∈ (paths i).support → w ∉ (paths j).support)

/--
Erdős Problem #915 (Bollobás–Erdős conjecture [BoEr62]):

Let G be a graph with 1 + n(m-1) vertices and at least 1 + n·C(m,2) edges.
Then G contains two vertices connected by m internally vertex-disjoint paths.

This was disproved by Leonard [Le73] for m = 5 and by Mader [Ma73] for all
m ≥ 6. The edge-disjoint analogue was confirmed by Mader.
-/
theorem erdos_problem_915 (n m : ℕ) (hm : m ≥ 2)
    (G : SimpleGraph (Fin (1 + n * (m - 1)))) [DecidableRel G.Adj]
    (hedge : G.edgeFinset.card ≥ 1 + n * m.choose 2) :
    ∃ u v : Fin (1 + n * (m - 1)), u ≠ v ∧
      HasInternallyDisjointPaths G u v m :=
  sorry

end
