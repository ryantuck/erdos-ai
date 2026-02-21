import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open SimpleGraph

/--
Erdős Problem #533 (Disproved):
Let δ > 0. If n is sufficiently large and G is a graph on n vertices with no K₅
and at least δn² edges, then G contains a set of ≫_δ n vertices containing no
triangle.

Equivalently, the conjecture asks whether δ₃(5) = 0, where δ₃(5) is the
Ramsey-Turán density. This was disproved by Balogh and Lenz [BaLe13], who
showed δ₃(5) > 0. The correct value is δ₃(5) = 1/12.
-/
theorem erdos_problem_533 :
    ∀ δ : ℝ, 0 < δ →
      ∃ c : ℝ, 0 < c ∧
        ∃ N : ℕ,
          ∀ n : ℕ, N ≤ n →
            ∀ G : SimpleGraph (Fin n),
              G.CliqueFree 5 →
              δ * (n : ℝ) ^ 2 ≤ (G.edgeSet.ncard : ℝ) →
                ∃ S : Finset (Fin n),
                  c * (n : ℝ) ≤ (S.card : ℝ) ∧
                  (G.induce (S : Set (Fin n))).CliqueFree 3 :=
  sorry
