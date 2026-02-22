import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

/-!
# Erdős Problem #661

Are there, for all large $n$, some points $x_1, \ldots, x_n, y_1, \ldots, y_n
\in \mathbb{R}^2$ such that the number of distinct distances $d(x_i, y_j)$ is
$o(n / \sqrt{\log n})$?

Tags: geometry | distances
-/

/-- The number of distinct bipartite distances between two finite point sets
    in ℝ², i.e., the number of distinct values dist(x, y) for x ∈ X, y ∈ Y. -/
noncomputable def bipartiteDistinctDistances
    (X Y : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {d : ℝ | ∃ x ∈ X, ∃ y ∈ Y, d = dist x y}

/--
**Erdős Problem #661** [ErPa90, Er92e, Er97e, Er97f]:

For all large n, there exist points x₁, ..., xₙ, y₁, ..., yₙ ∈ ℝ² such that
the number of distinct bipartite distances d(xᵢ, yⱼ) is o(n / √(log n)).

Formulated as: for every ε > 0, there exists N such that for all n ≥ N,
there exist X, Y ⊂ ℝ² with |X| = n, |Y| = n, and the number of distinct
bipartite distances is at most ε · n / √(log n).
-/
theorem erdos_problem_661 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ X Y : Finset (EuclideanSpace ℝ (Fin 2)),
          X.card = n ∧ Y.card = n ∧
          (bipartiteDistinctDistances X Y : ℝ) ≤
            ε * (n : ℝ) / Real.sqrt (Real.log (n : ℝ)) :=
  sorry

end
