import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.InnerProductSpace.PiL2

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1007

The dimension of a graph G is the minimal n such that G can be embedded in ℝⁿ
such that every edge of G is a unit line segment (adjacent vertices are at
Euclidean distance exactly 1, and non-adjacent vertices are not). This notion
was defined by Erdős, Harary, and Tutte.

What is the smallest number of edges in a graph with dimension 4?

The answer is 9, achieved uniquely by K_{3,3}. Proved by House [Ho13], with
an alternative proof by Chaffee and Noble [ChNo16].
-/

/-- A unit-distance representation of a simple graph G in ℝⁿ: an injective map
    from vertices to Euclidean n-space such that adjacency is equivalent to
    distance exactly 1. -/
def IsUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (f : V → EuclideanSpace ℝ (Fin n)) : Prop :=
  Function.Injective f ∧
  ∀ u v, G.Adj u v ↔ dist (f u) (f v) = 1

/-- A graph admits a unit-distance representation in ℝⁿ. -/
def HasUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), IsUnitDistRep G n f

/--
Erdős Problem #1007 [So09e]:

The smallest number of edges in a graph of dimension exactly 4 is 9, where the
dimension of a graph is the minimal n for a unit-distance representation in ℝⁿ.

This is achieved uniquely by K_{3,3}. Proved by House [Ho13].
-/
theorem erdos_problem_1007 :
    -- There exists a graph of dimension exactly 4 with 9 edges
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
       (_ : DecidableRel G.Adj),
       HasUnitDistRep G 4 ∧ ¬HasUnitDistRep G 3 ∧ G.edgeFinset.card = 9) ∧
    -- Every graph of dimension exactly 4 has at least 9 edges
    (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
       [DecidableRel G.Adj],
       HasUnitDistRep G 4 → ¬HasUnitDistRep G 3 → 9 ≤ G.edgeFinset.card) :=
  sorry

end
