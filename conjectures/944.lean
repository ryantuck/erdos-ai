import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic

open SimpleGraph

/--
A graph G with chromatic number k is k-vertex-critical if deleting any single
vertex strictly reduces the chromatic number.
-/
def SimpleGraph.IsVertexCritical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧
  ∀ v : V, (G.induce (· ≠ v)).chromaticNumber < (k : ℕ∞)

/--
A set of edges S is critical for G if deleting S strictly reduces the
chromatic number.
-/
def SimpleGraph.IsCriticalEdgeSet {V : Type*} (G : SimpleGraph V)
    (S : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges ↑S).chromaticNumber < G.chromaticNumber

/--
Erdős Problem #944 [Er89e]:

Let k ≥ 4 and r ≥ 1. Must there exist a graph G with chromatic number k such
that every vertex is critical (i.e. G is k-vertex-critical), yet every critical
set of edges has size > r?

Dirac conjectured this for k ≥ 4 and r = 1 in 1970. Brown proved the case k = 5.
Jensen gave constructions for all k ≥ 5. Skottova and Steiner proved this for
all k ≥ 5 and r ≥ 1. The case k = 4 remains open (even for r = 1).
-/
theorem erdos_problem_944 (k : ℕ) (hk : k ≥ 4) (r : ℕ) (hr : r ≥ 1) :
    ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
      G.IsVertexCritical k ∧
      ∀ S : Finset (Sym2 (Fin n)), S.card ≤ r → ¬G.IsCriticalEdgeSet S :=
  sorry
