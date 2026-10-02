-- [AI - Claude Opus 5.5]: Erdős Problem 96 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

open Filter

/-!
# Erdős Problem #96

*Source:* [erdosproblems.com/96](https://www.erdosproblems.com/96) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; page last edited 23 January
2026, captured 2026-02-23). [Er90] [Er92e] [Er97e] [Er97f] [Va99, 4.68]

If $n$ points in $\mathbb{R}^2$ form a convex polygon then there are $O(n)$ many pairs which
are distance $1$ apart.

Remarks recorded on the page:
* Conjectured by Erdős and Moser. In [Er92e] Erdős credits himself and Fishburn with the
  conjecture that the true upper bound is $2n$.
* Füredi [Fu90] proved an upper bound of $O(n \log n)$; a short proof was given by Brass and
  Pach [BrPa01]. The best known upper bound is $\le n \log_2 n + 4n$, due to Aggarwal [Ag15].
* Edelsbrunner and Hajnal [EdHa91] constructed $n$ such points with $2n - 7$ pairs at
  distance 1. This disproved an early stronger conjecture of Erdős and Moser, that the true
  answer was $\frac{5}{3} n + O(1)$.
* A positive answer would follow from Problem #97. See also Problem #90.
* In [Er92e] Erdős makes the stronger conjecture that, if $g(x)$ counts the largest number of
  points of $A$ equidistant from $x$, then $\sum_{x \in A} g(x) < 4n$. He notes that the
  Edelsbrunner–Hajnal example shows $\sum_{x \in A} g(x) > 4n - O(1)$ is possible.

**Encoding.** `unitDistancePairCount` counts *ordered* pairs, which is twice the number of
unit-distance pairs in the page's sense. The $O(n)$ statement absorbs the factor 2. The
variants with explicit constants double them.

Tags: geometry, distances, convex. OEIS: "possible".

## References

* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
  "Paul Erdős and his mathematics", Budapest, July 1999.
* [Fu90] Füredi, Z., _The maximum number of unit distances in a convex n-gon_. J. Combin.
  Theory Ser. A (1990), 316–320.
* [BrPa01] Brass, P. and Pach, J., _The maximum number of times the same distance can occur
  among the vertices of a convex n-gon is O(n log n)_. J. Combin. Theory Ser. A (2001),
  178–179.
* [Ag15] Aggarwal, A., _On unit distances in a convex polygon_. Discrete Math. (2015),
  88–92.
* [EdHa91] Edelsbrunner, H. and Hajnal, P., _A lower bound on the number of unit distances
  between the vertices of a convex polygon_. J. Combin. Theory Ser. A (1991), 312–316.

(Provenance: the original pipeline's `/latex` fetches. [Fu90], [BrPa01], [Ag15] and [EdHa91]
come from the fetch of `erdosproblems.com/latex/96`. [Er90] from `/latex/91`, [Er92e] from
`/latex/94`, [Er97e] from `/latex/654`, and [Er97f] and [Va99] from several sibling
extractions, which agree.)
-/

/--
A finite set of points in ℝ² is in convex position if no point lies in the
convex hull of the remaining points. Equivalently, the points are the vertices
of a convex polygon.
-/
def ConvexPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ P, p ∉ convexHull ℝ (↑(P.erase p) : Set (EuclideanSpace ℝ (Fin 2)))

/--
The number of ordered pairs of distinct points in P that are at unit distance.
(Using ordered pairs; the number of unordered pairs is exactly half this,
so the O(n) bound is equivalent.)
-/
noncomputable def unitDistancePairCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/--
Erdős Problem #96 (Erdős–Moser conjecture, OPEN):
If n points in ℝ² form a convex polygon (are in convex position), then there
are O(n) many pairs which are distance 1 apart.

Formally: there exists an absolute constant C > 0 such that for every finite
set P of points in ℝ² in convex position, the number of (ordered) pairs at
unit distance is at most C · |P|.
-/
theorem erdos_problem_96 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      (unitDistancePairCount P : ℝ) ≤ C * (P.card : ℝ) := by
  sorry

/--
Aggarwal [Ag15] (PROVED): a convex polygon has at most $n \log_2 n + 4n$ unit-distance pairs,
so at most twice that many ordered pairs. This sharpens Füredi's $O(n \log n)$ [Fu90]; see
also [BrPa01]. At `n = 0` both sides are `0`.
-/
theorem erdos_problem_96.variants.aggarwal :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P →
      (unitDistancePairCount P : ℝ) ≤
        2 * ((P.card : ℝ) * Real.logb 2 (P.card : ℝ) + 4 * (P.card : ℝ)) := by
  sorry

/--
Edelsbrunner and Hajnal [EdHa91] (PROVED): there are convex `n`-gons with $2n - 7$
unit-distance pairs. The page's wording suggests a construction for every `n`. Only the
weaker "for arbitrarily large `n`" is asserted here, written without ℕ subtraction:
$2(2n - 7) \le$ the ordered count, i.e. $4n \le$ count $+ 14$.
-/
theorem erdos_problem_96.variants.edelsbrunner_hajnal :
    ∃ᶠ n : ℕ in atTop, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card = n ∧ ConvexPosition P ∧ 4 * n ≤ unitDistancePairCount P + 14 := by
  sorry

/--
The Erdős–Fishburn conjecture [Er92e] (OPEN): the true upper bound is $2n$ unit-distance
pairs, i.e. at most $4n$ ordered pairs.
-/
theorem erdos_problem_96.variants.two_n :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      ConvexPosition P → unitDistancePairCount P ≤ 4 * P.card := by
  sorry

/--
The largest number of other points of `P` on one circle centred at `x`, i.e. the largest
number of points of `P` equidistant from `x`.
-/
noncomputable def maxEquidistantFrom (P : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  P.sup (fun y => ((P.erase x).filter (fun z => dist x z = dist x y)).card)

/--
Erdős's stronger conjecture [Er92e] (OPEN): for a nonempty convex polygon,
$\sum_{x \in A} g(x) < 4n$, where $g(x)$ is the largest number of points equidistant from
`x`. Since each ordered unit pair is counted in some $g(x)$, this implies
`erdos_problem_96.variants.two_n`, with strict inequality. Nonemptiness is needed because
$0 < 0$ is false.
-/
theorem erdos_problem_96.variants.sum_equidistant :
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2))),
      P.Nonempty → ConvexPosition P →
      ∑ x ∈ P, maxEquidistantFrom P x < 4 * P.card := by
  sorry
