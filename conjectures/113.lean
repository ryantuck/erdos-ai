import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

open SimpleGraph

/-- An injective graph homomorphism from H to F; witnesses that F contains a
    subgraph isomorphic to H. -/
def containsSubgraph {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj],
    Fintype.card V = n ∧ ¬containsSubgraph F H ∧ F.edgeFinset.card = m}

/-- A graph G is 2-degenerate if every non-empty finite set of vertices contains
    a vertex with at most 2 neighbors within that set.  Equivalently, G has no
    induced subgraph with minimum degree at least 3. -/
def IsTwoDegenerateGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ 2

/--
Erdős-Simonovits Conjecture (Problem #113) [ErSi84]:
For a bipartite graph G on a finite vertex set, the Turán number satisfies

  ex(n; G) ≪ n^{3/2}

if and only if G is 2-degenerate (i.e., G has no induced subgraph with minimum
degree at least 3).

Here ex(n; G) ≪ n^{3/2} means there exists a constant C > 0 such that
ex(n; G) ≤ C · n^{3/2} for all n.

DISPROVED by Janzer [Ja23b]: for any ε > 0, there exists a 3-regular bipartite
graph H such that ex(n; H) ≪ n^{4/3 + ε}. Since a 3-regular graph is not
2-degenerate but its Turán number is still o(n^{3/2}), the "only if" direction
(ex(n; G) ≪ n^{3/2} → G is 2-degenerate) fails.
-/
theorem erdos_problem_113 :
    ∀ (U : Type*) (G : SimpleGraph U) [Fintype U] [DecidableRel G.Adj],
      Nonempty (G.Coloring (Fin 2)) →
      (IsTwoDegenerateGraph G ↔
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          (turanNumber G n : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)) :=
  sorry
