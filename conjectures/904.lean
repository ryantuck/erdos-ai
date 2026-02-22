import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card

open SimpleGraph

/--
Erdős Problem #904 (Bollobás-Erdős conjecture, proved by Edwards [Ed78]):
If G is a graph with n vertices and more than n²/4 edges, then G contains a
triangle on vertices x, y, z such that d(x) + d(y) + d(z) ≥ 3n/2.
-/
theorem erdos_problem_904 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (n : ℝ) ^ 2 / 4 < (G.edgeFinset.card : ℝ) →
      ∃ x y z : Fin n, G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
        (G.degree x + G.degree y + G.degree z : ℝ) ≥ 3 / 2 * (n : ℝ) :=
  sorry
