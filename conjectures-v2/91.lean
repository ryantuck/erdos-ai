import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 91

Let $n$ be a sufficiently large integer. Suppose $A \subset \mathbb{R}^2$ has $|A| = n$
and minimises the number of distinct distances between points in $A$. Prove that there
are at least two (and probably many) such $A$ which are non-similar.

This is an **open** problem (as of the source page's last edit, 16 January 2026).

## Remarks

For $n = 3$ the equilateral triangle is the only such set. For $n = 4$ the square or two
equilateral triangles sharing an edge give two non-similar examples. For $n = 5$ the
regular pentagon is the unique such set (which has two distinct distances). Erdős
mysteriously remarks in [Er90] this was proved by "a colleague" (in [Er87b] described as
"a colleague from Zagreb"). A published proof is provided by Kovács [Ko24c]. In [Er87b]
Erdős says that there are at least two non-similar examples for $6 \le n \le 9$.

The minimal possible number of distinct distances is the subject of problem [89].

Related OEIS sequence: A186704 (possible).

## References

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_.
Intuitive geometry (Siófok, 1985) (1987), 167–177.

[Er90] Erdős, Paul, _Some of my favourite unsolved problems_.
A tribute to Paul Erdős (1990), 467–478.

[Er97e] Erdős, P., (1997). (stub — journal/volume/pages not recovered)

[Ko24c] Z. Kovács, _A note on Erdős's mysterious remark_. arXiv:2412.05190 (2024).
-/

open Finset Classical

/--
The number of distinct positive distances determined by a finite point set A in ℝ².
-/
noncomputable def numDistinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  A.offDiag.image (fun pq => dist pq.1 pq.2) |>.card

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

/--
Erdős Problem 91, variant: for $n = 5$, the regular pentagon is the unique minimiser
of the number of distinct distances (up to similarity). Proved by Kovács [Ko24c].
-/
theorem erdos_problem_91_n5_unique
    (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (hA : A.card = 5)
    (hmin : ∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = 5 →
      numDistinctDistances A ≤ numDistinctDistances B)
    (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (hP : P.card = 5)
    (hPmin : ∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = 5 →
      numDistinctDistances P ≤ numDistinctDistances B) :
    AreSimilar A P := by
  sorry

/--
Erdős Problem 91, variant: for $n = 4$, there exist two non-similar minimisers of
the number of distinct distances (the square and two equilateral triangles sharing
an edge). Known; see [Er87b].
-/
theorem erdos_problem_91_n4_two_minimisers :
    ∃ A A' : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 4 ∧ A'.card = 4 ∧
      (∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = 4 →
        numDistinctDistances A ≤ numDistinctDistances B) ∧
      (∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = 4 →
        numDistinctDistances A' ≤ numDistinctDistances B) ∧
      ¬ AreSimilar A A' := by
  sorry
