import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open SimpleGraph Cardinal

/--
A graph G (on vertex type V) has chromatic number ℵ₁ if it cannot be properly
colored with countably many colors but can be properly colored with ℵ₁ colors.
-/
def HasChromaticNumberAleph1 {V : Type*} (G : SimpleGraph V) : Prop :=
  (∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) ∧
  (∃ α : Type*, #α = aleph 1 ∧ Nonempty (G.Coloring α))

/--
The minimum number of edges that must be deleted from a finite graph H to make
it bipartite (i.e., properly 2-colorable).
-/
noncomputable def minEdgeDeletionsForBipartite {W : Type*} [Fintype W]
    (H : SimpleGraph W) : ℕ :=
  sInf {k : ℕ | ∃ H' : SimpleGraph W,
    H' ≤ H ∧
    Nonempty (H'.Coloring (Fin 2)) ∧
    (H.edgeSet \ H'.edgeSet).ncard = k}

/--
For a graph G and n : ℕ, hFun G n is defined as the maximum over all n-vertex
induced subgraphs H of G of the minimum number of edges that must be deleted
from H to make it bipartite.

That is, hFun G n is the smallest k such that every induced subgraph of G on
exactly n vertices can be made bipartite by deleting at most k edges.
-/
noncomputable def hFun {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (S : Finset V),
    S.card = n ∧
    k = minEdgeDeletionsForBipartite (G.induce (S : Set V))}

/--
Erdős's Conjecture (Problem #111):
There exists a graph G with chromatic number ℵ₁ such that hFun G n ≪ n^{1+ε}
for every ε > 0.

Background:
- For every G with chromatic number ℵ₁, hFun G n ≫ n, since G must contain ℵ₁
  many vertex-disjoint odd cycles of some fixed length 2r+1.
- Erdős–Hajnal–Szemerédi [EHS82] proved there exists G with chromatic number ℵ₁
  satisfying hFun G n ≪ n^{3/2}.
- Erdős [Er81] conjectured this upper bound can be improved: there should exist G
  with chromatic number ℵ₁ such that hFun G n ≪ n^{1+ε} for every ε > 0.
-/
theorem erdos_problem_111 :
    ∃ (V : Type*) (G : SimpleGraph V),
      HasChromaticNumberAleph1 G ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ n : ℕ, (hFun G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε) :=
  sorry
