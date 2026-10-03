-- [AI - Claude Opus 5.5]: Erdős Problem 91 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset Classical

/-!
# Erdős Problem #91

*Source:* [erdosproblems.com/91](https://www.erdosproblems.com/91) (status **OPEN**:
"This is open, and cannot be resolved with a finite computation."; page last edited
16 January 2026, captured 2026-02-22). [Er87b, p.171] [Er90] [Er97e]

Let $n$ be a sufficiently large integer. Suppose $A \subset \mathbb{R}^2$ has $|A| = n$ and
minimises the number of distinct distances between points in $A$. Prove that there are at
least two (and probably many) such $A$ which are non-similar.

Remarks recorded on the page:
* For $n = 3$ the equilateral triangle is the only such set. For $n = 4$ the square, or two
  equilateral triangles sharing an edge, give two non-similar examples.
* For $n = 5$ the regular pentagon is the unique such set (it has two distinct distances).
  Erdős remarks in [Er90] that this was proved by "a colleague" (in [Er87b], "a colleague
  from Zagreb"); a published proof is given by Kovács [Ko24c].
* In [Er87b] Erdős says that there are at least two non-similar examples for $6 \le n \le 9$.
* The minimal possible number of distinct distances is the subject of Problem #89.

**Encoding.** `erdos_problem_91` says that every $n$-point minimiser $A$ has a non-similar
$n$-point minimiser $A'$. For each $n$ a minimiser exists (a nonempty set of naturals has a
least element), and `AreSimilar` is an equivalence relation (a distance-scaling self-map of
the plane is a bijective similarity). So the statement is equivalent to "there are two
non-similar minimisers".

Tags: geometry, distances. OEIS: A186704 ("possible").

## References

* [Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive
  geometry (Siófok, 1985) (1987), 167–177.
* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.
* [Ko24c] Kovács, Z., _A note on Erdős's mysterious remark_. arXiv:2412.05190 (2024).

(Provenance: [Er87b], [Er90] and [Ko24c] come from the original pipeline's fetch of
`erdosproblems.com/latex/91`. [Er97e] comes from the fetches of `/latex/654`, `/latex/132`,
`/latex/604`, `/latex/657` and `/latex/658`, which agree on the title. Only `/latex/654`
gives the journal and pages. Some sibling files in this repository gloss [Er97e] with other
titles; those glosses are not used.)
-/

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
Erdős Problem #91 (OPEN):
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
`A` has exactly `n` points and determines the fewest distinct distances among all `n`-point
subsets of ℝ². This is the hypothesis of `erdos_problem_91`, packaged for the variants below.
-/
def IsDistinctDistanceMinimiser (n : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  A.card = n ∧
    ∀ B : Finset (EuclideanSpace ℝ (Fin 2)), B.card = n →
      numDistinctDistances A ≤ numDistinctDistances B

/--
For $n = 3$ the equilateral triangle is the only minimiser, so any two 3-point minimisers
are similar. (True and elementary: the minimum is 1, and a 3-point set with one distance is
an equilateral triangle.)
-/
theorem erdos_problem_91.variants.three :
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      IsDistinctDistanceMinimiser 3 A → IsDistinctDistanceMinimiser 3 B → AreSimilar A B :=
  sorry

/--
For $n = 4$ there are two non-similar minimisers: the square and the rhombus made of two
equilateral triangles sharing an edge. Both determine 2 distances, and no 4-point set in the
plane determines only 1.
-/
theorem erdos_problem_91.variants.four :
    ∃ A A' : Finset (EuclideanSpace ℝ (Fin 2)),
      IsDistinctDistanceMinimiser 4 A ∧ IsDistinctDistanceMinimiser 4 A' ∧ ¬ AreSimilar A A' :=
  sorry

/--
For $n = 5$ the regular pentagon is the unique minimiser (Kovács [Ko24c]), so any two 5-point
minimisers are similar.
-/
theorem erdos_problem_91.variants.five :
    ∀ A B : Finset (EuclideanSpace ℝ (Fin 2)),
      IsDistinctDistanceMinimiser 5 A → IsDistinctDistanceMinimiser 5 B → AreSimilar A B :=
  sorry

/--
Erdős [Er87b] says that for $6 \le n \le 9$ there are at least two non-similar minimisers.
Candidate pairs, each pair with equal counts: the regular hexagon and the regular pentagon
with its centre (3 distances each, $n = 6$); the regular heptagon and the regular hexagon with
its centre (3, $n = 7$); the regular octagon and the regular heptagon with its centre (4,
$n = 8$); the regular 9-gon and a 9-point piece of the triangular lattice (4, $n = 9$).
These counts are minimal if the classification of planar 2- and 3-distance sets is used.
-/
theorem erdos_problem_91.variants.six_to_nine :
    ∀ n : ℕ, 6 ≤ n → n ≤ 9 →
      ∃ A A' : Finset (EuclideanSpace ℝ (Fin 2)),
        IsDistinctDistanceMinimiser n A ∧ IsDistinctDistanceMinimiser n A' ∧
          ¬ AreSimilar A A' :=
  sorry

/--
The parenthetical "(and probably many)" (OPEN, and stronger than the main statement): for
every $k$, every sufficiently large $n$ has $k$ pairwise non-similar $n$-point minimisers.
At $k = 2$ this is equivalent to `erdos_problem_91`.
-/
theorem erdos_problem_91.variants.many :
    ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Fin k → Finset (EuclideanSpace ℝ (Fin 2)),
        (∀ i, IsDistinctDistanceMinimiser n (A i)) ∧
          ∀ i j, i ≠ j → ¬ AreSimilar (A i) (A j) :=
  sorry
