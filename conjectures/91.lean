import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Classical

/--
The number of distinct positive distances determined by a finite point set A in ℝ².
-/
noncomputable def numDistinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((A ×ˢ A).filter (fun pq => pq.1 ≠ pq.2)).image (fun pq => dist pq.1 pq.2) |>.card

/--
Two finite point sets in ℝ² are similar if there exists a map f : ℝ² → ℝ² that
scales all distances by the same positive constant r and maps one set onto the other.
-/
def AreSimilar (A B : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ (f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) (r : ℝ),
    r > 0 ∧
    (∀ x y : EuclideanSpace ℝ (Fin 2), dist (f x) (f y) = r * dist x y) ∧
    (∀ a, a ∈ A → f a ∈ B) ∧
    (∀ b, b ∈ B → ∃ a ∈ A, f a = b)

/--
Erdős Problem #91:
For sufficiently large n, if A ⊂ ℝ² has |A| = n and minimises the number of
distinct distances, then there exists another minimiser A' of the same cardinality
that is not similar to A. In other words, there are at least two non-similar
sets that minimise the number of distinct distances.
-/
theorem erdos_problem_91 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n →
      (∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n →
        numDistinctDistances A ≤ numDistinctDistances B) →
      ∃ A' : Finset (EuclideanSpace ℝ (Fin 2)),
        A'.card = n ∧
        (∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n →
          numDistinctDistances A' ≤ numDistinctDistances B) ∧
        ¬ AreSimilar A A' :=
  sorry
