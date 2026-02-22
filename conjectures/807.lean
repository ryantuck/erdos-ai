import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.SetTheory.Cardinal.Finite

noncomputable section

open SimpleGraph Filter Topology Classical

/--
A biclique cover of a simple graph G of size k consists of k complete bipartite
subgraphs (specified by pairs of disjoint vertex sets) that are pairwise
edge-disjoint and together cover all edges of G.
-/
def IsBicliqueCover {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (A B : Fin k → Set V) : Prop :=
  (∀ i, Disjoint (A i) (B i)) ∧
  (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, G.Adj a b) ∧
  (∀ i j : Fin k, i ≠ j →
    ∀ v w : V, ¬((v ∈ A i ∧ w ∈ B i ∨ w ∈ A i ∧ v ∈ B i) ∧
                  (v ∈ A j ∧ w ∈ B j ∨ w ∈ A j ∧ v ∈ B j))) ∧
  (∀ v w : V, G.Adj v w →
    ∃ i : Fin k, (v ∈ A i ∧ w ∈ B i) ∨ (w ∈ A i ∧ v ∈ B i))

/--
The bipartition number τ(G) is the minimum number of pairwise edge-disjoint
complete bipartite subgraphs needed to cover all edges of G.
-/
def bipartitionNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (A B : Fin k → Set V), IsBicliqueCover G k A B}

/--
The independence number α(G) of a finite graph is the maximum cardinality of
an independent set (a set of vertices with no edges between them).
-/
def independenceNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset V, S.card = k ∧
    ∀ v ∈ S, ∀ w ∈ S, v ≠ w → ¬G.Adj v w}

/--
Erdős Problem #807 (disproved by Alon [Al15]):

Is it true that for a random graph G on n vertices with edge probability 1/2,
τ(G) = n − α(G) almost surely?

The bipartition number τ(G) is the smallest number of pairwise edge-disjoint
complete bipartite graphs whose union is G. The independence number α(G) is
the size of the largest independent set in G.

In the G(n, 1/2) model every labeled graph on n vertices is equally likely, so
"almost surely" means the proportion of graphs satisfying the property tends
to 1 as n → ∞.

Alon [Al15] showed this is false: almost surely τ(G) ≤ n − α(G) − 1.
Alon, Bohman, and Huang [ABH17] proved there exists c > 0 such that
almost surely τ(G) ≤ n − (1 + c)α(G).
-/
theorem erdos_problem_807 :
    Tendsto (fun n : ℕ =>
      (Nat.card {G : SimpleGraph (Fin n) //
        bipartitionNumber G = n - independenceNumber G} : ℝ) /
      (Nat.card (SimpleGraph (Fin n)) : ℝ))
    atTop (nhds 1) :=
  sorry

end
