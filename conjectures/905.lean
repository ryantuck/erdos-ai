import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

open SimpleGraph Finset

/--
Erdős Problem #905 (Bollobás-Erdős conjecture):
Every graph with n vertices and more than n²/4 edges contains an edge
which is in at least n/6 triangles.

A triangle containing edge {u, v} corresponds to a common neighbor of u and v,
i.e., a vertex w adjacent to both u and v.
-/
theorem erdos_problem_905 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.edgeFinset.card : ℝ) > (n : ℝ) ^ 2 / 4 →
    ∃ u v : Fin n, G.Adj u v ∧
      ((G.neighborFinset u ∩ G.neighborFinset v).card : ℝ) ≥ (n : ℝ) / 6 :=
sorry
