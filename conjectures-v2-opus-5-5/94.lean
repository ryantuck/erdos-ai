-- [AI - Claude Opus 5.5]: Erdős Problem 94 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Filter

/-!
# Erdős Problem #94

*Source:* [erdosproblems.com/94](https://www.erdosproblems.com/94) (status **PROVED (LEAN)**:
"This has been solved in the affirmative and the proof verified in Lean."; prize £25, shown
on the page as \$44; page last edited 28 December 2025, captured 2026-02-22). [Er92e]
[Er95, p.181] [Er97c] [Er97f]

Suppose $n$ points in $\mathbb{R}^2$ determine a convex polygon and the set of distances
between them is $\{u_1, \ldots, u_t\}$. Suppose $u_i$ appears as the distance between
$f(u_i)$ many pairs of points. Then $\sum_i f(u_i)^2 \ll n^3$.

Remarks recorded on the page:
* In [Er97c] Erdős claims that Fishburn solved this, but gives no reference. It is trivial
  that $\sum_i f(u_i) = \binom{n}{2}$.
* Lefmann and Thiele [LeTh95] prove the stronger statement that $\sum_i f(u_i)^2 \ll n^3$
  under the weaker assumption that no three points are on a line. (The page's remark spells
  the name "Theile"; its bibliography has Thiele.) A sketch of the proof is given in the
  page's comments by serge.
* Erdős and Fishburn also conjecture that $\sum_i f(u_i)^2$ is maximal for the regular
  $n$-gon, for large enough $n$.
* In [Er92e] Erdős offered £25 for a resolution of this problem.
* See also Problem #95.

**Encoding.** `distSqSum A` counts ordered quadruples $(a, b, c, d)$ with $a \ne b$, $c \ne d$
and $|ab| = |cd|$. Each distance $u$ is realised by $2 f(u)$ ordered pairs, so
`distSqSum A` $= \sum_u (2 f(u))^2 = 4 \sum_u f(u)^2$, and the factor 4 is absorbed by the
constant. For the regular $n$-gon, $\sum_u f(u)^2 \sim n^3/2$, so the exponent 3 is sharp.

Tags: geometry, convex, distances. OEIS: A387858.

## References

* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97c] Erdős, P., _Some of my favorite problems and results_. The mathematics of Paul
  Erdős, I (1997), 47–67.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [LeTh95] Lefmann, H. and Thiele, T., _Point sets with distinct distances_. Combinatorica
  (1995), 379–408.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/94` for [Er92e],
[Er97c] and [LeTh95]; `/latex/75` and `/latex/843` for [Er95]; `/latex/1082` and others for
[Er97f]. All agree with upstream formal-conjectures at `df3f12d`.)
-/

/--
A finite set of points in ℝ² is in convex position if no point lies in
the convex hull of the remaining points. Equivalently, all points are
vertices of their convex hull (they form a convex polygon).
-/
def ConvexPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A : Set (EuclideanSpace ℝ (Fin 2))) \ {p})

/--
The count of ordered quadruples (a, b, c, d) from A with a ≠ b, c ≠ d,
and dist(a, b) = dist(c, d). This equals 4 · ∑ᵢ f(uᵢ)² where f(uᵢ)
counts unordered pairs at distance uᵢ.
-/
noncomputable def distSqSum (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  let E := EuclideanSpace ℝ (Fin 2)
  Set.ncard {x : E × E × E × E |
    x.1 ∈ (A : Set E) ∧ x.2.1 ∈ (A : Set E) ∧
    x.2.2.1 ∈ (A : Set E) ∧ x.2.2.2 ∈ (A : Set E) ∧
    x.1 ≠ x.2.1 ∧ x.2.2.1 ≠ x.2.2.2 ∧
    dist x.1 x.2.1 = dist x.2.2.1 x.2.2.2}

/--
Erdős Problem #94 (PROVED):
Suppose n points in ℝ² are in convex position (they form the vertices of
a convex polygon). Let {u₁, ..., uₜ} be the set of distinct pairwise
distances, and let f(uᵢ) denote the number of pairs at distance uᵢ. Then
  ∑ᵢ f(uᵢ)² ≪ n³.

This was proved by Lefmann and Thiele [LeTh95] under the weaker
assumption that no three points are collinear.
-/
theorem erdos_problem_94 :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      ConvexPosition A →
      (distSqSum A : ℝ) ≤ C * (A.card : ℝ) ^ 3 :=
  sorry

open Classical in
/--
Sanity check of the encoding: `distSqSum A` is the sum, over distinct distances `u`, of the
square of the number of ordered pairs at distance `u` (that number is `2 f(u)`).
-/
theorem erdos_problem_94.distSqSum_eq_sum_sq (A : Finset (EuclideanSpace ℝ (Fin 2))) :
    distSqSum A = ∑ u ∈ A.offDiag.image (fun pq => dist pq.1 pq.2),
      ((A.offDiag.filter (fun pq => dist pq.1 pq.2 = u)).card) ^ 2 :=
  sorry

/--
No three points of `A` are collinear.
-/
def NoThreeCollinear (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))

/--
Lefmann and Thiele [LeTh95] (PROVED): $\sum_i f(u_i)^2 \ll n^3$ already holds when no three
points are on a line. Points in convex position have no three on a line, so this implies
`erdos_problem_94`.
-/
theorem erdos_problem_94.variants.no_three_collinear :
    ∃ C : ℝ, C > 0 ∧
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      NoThreeCollinear A →
      (distSqSum A : ℝ) ≤ C * (A.card : ℝ) ^ 3 :=
  sorry

/--
The vertices of the regular `n`-gon inscribed in the unit circle.
-/
noncomputable def regularNGon (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  (Finset.range n).image fun k : ℕ =>
    !₂[Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

/--
The Erdős–Fishburn conjecture (OPEN): for all large `n`, among `n` points in convex
position, $\sum_i f(u_i)^2$ is maximised by the regular `n`-gon.
-/
theorem erdos_problem_94.variants.regular_ngon_maximal :
    ∀ᶠ n : ℕ in atTop, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = n → ConvexPosition A → distSqSum A ≤ distSqSum (regularNGon n) :=
  sorry
