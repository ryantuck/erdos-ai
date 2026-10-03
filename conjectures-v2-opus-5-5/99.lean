-- [AI - Claude Opus 5.5]: Erdős Problem 99 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open scoped NNReal

/-!
# Erdős Problem #99

*Source:* [erdosproblems.com/99](https://www.erdosproblems.com/99) (status **OPEN**, \$100:
"This is open, and cannot be resolved with a finite computation."; captured 2026-03-05; the
capture shows no "last edited" line). [Er94b] [Er95] [Er97e]

Let $A \subseteq \mathbb{R}^2$ be a set of $n$ points with minimum distance equal to 1, chosen
to minimise the diameter of $A$. If $n$ is sufficiently large then must there be three points
in $A$ which form an equilateral triangle of size 1?

Remarks recorded on the page:
* Thue proved that the minimal such diameter is achieved (asymptotically) by the points in a
  triangular lattice intersected with a circle. In general Erdős believed such a set must
  have very large intersection with the triangular lattice, perhaps as many as $(1-o(1))n$
  points.
* Erdős [Er94b] wrote "I could not prove it but felt that it should not be hard. To my great
  surprise both B. H. Sendov and M. Simonovits doubted the truth of this conjecture." In
  [Er94b] he offers \$100 for a counterexample but only \$50 for a proof.
* The stated problem is false for $n = 4$, e.g. the vertices of a square. Bezdek and Fodor
  [BeFo99] explore the behaviour of such sets for small $n$.
* See also Problem #103.

**Encoding.** Requiring minimum distance $\ge 1$ instead of $= 1$, both for $A$ and for the
competitors, changes nothing. Any admissible set can be rescaled to minimum distance exactly
1 without increasing its diameter, so diameter minimisers have minimum distance exactly 1.
Minimisers exist for every $n \ge 2$ by compactness.

Tags: geometry, distances.

## References

* [Er94b] Erdős, P., _Some problems in number theory, combinatorics and combinatorial
  geometry_. Math. Pannon. (1994), 261–269.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97e] Erdős, P., _Some of my favourite unsolved problems_. Math. Japon. (1997),
  527–537.
* [BeFo99] Bezdek, A. and Fodor, F., _Minimal diameter of certain sets in the plane_.
  J. Combin. Theory Ser. A (1999), 105–111.

(Provenance: [Er94b], [Er95] and [Er97e] come from the original pipeline's `/latex`
extractions for sibling problems (106/755, 75/843, 654). [BeFo99] comes from upstream
formal-conjectures `ErdosProblems/99.lean` at `df3f12d`, whose [Er94b] entry agrees.)
-/

/--
The minimum pairwise distance of a finite set of points, or the junk value `0` if the set
has fewer than two points. (The first-pass version discharged the nonemptiness obligation
with `sorry`; this one is total.)
-/
noncomputable def minPairwiseDist {α : Type*} [Dist α] (A : Finset α) : ℝ :=
  if h : (A.offDiag.image (fun p => dist p.1 p.2)).Nonempty then
    (A.offDiag.image (fun p => dist p.1 p.2)).min' h
  else 0

/--
The diameter of a finite set of points (maximum pairwise distance), or `0` if the set has
fewer than two points, which agrees with `Metric.diam` there.
-/
noncomputable def diameter {α : Type*} [Dist α] (A : Finset α) : ℝ :=
  if h : (A.offDiag.image (fun p => dist p.1 p.2)).Nonempty then
    (A.offDiag.image (fun p => dist p.1 p.2)).max' h
  else 0

/--
Three points form an equilateral triangle of side length s.
-/
def IsEquilateralTriangle (a b c : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : Prop :=
  dist a b = s ∧ dist b c = s ∧ dist a c = s

/--
A finite set A achieves the minimum diameter among all n-point subsets of ℝ²
with minimum pairwise distance at least 1. Sets with fewer than two points never qualify,
since their `minPairwiseDist` is `0`.
-/
def MinimisesDiameter (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  minPairwiseDist A ≥ 1 ∧
  ∀ B : Finset (EuclideanSpace ℝ (Fin 2)),
    B.card = A.card →
    minPairwiseDist B ≥ 1 →
    diameter A ≤ diameter B

/--
Erdős Problem #99 [Er94b, Er95, Er97e] (OPEN, \$100 for a counterexample):

Let A ⊆ ℝ² be a set of n points with minimum distance equal to 1, chosen to
minimise the diameter of A. If n is sufficiently large then must there be three
points in A which form an equilateral triangle of side length 1?

Thue proved that the minimal diameter is achieved (asymptotically) by points in
a triangular lattice intersected with a circle. Erdős believed such a set must
have very large intersection with the triangular lattice.

The conjecture is false for small n (e.g., n = 4 with square vertices).
-/
theorem erdos_problem_99 :
    ∃ N₀ : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      A.card ≥ N₀ →
      MinimisesDiameter A →
      ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A,
        a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
        IsEquilateralTriangle a b c 1 :=
  sorry

/--
The page's small case (PROVED, elementary): for $n = 4$ the unit square minimises the
diameter ($\sqrt2$) but contains no unit equilateral triangle. Four points at mutual distance
$\ge 1$ have diameter $\ge \sqrt2$: either some angle of the convex hull is $\ge 90°$, or one
point lies inside the triangle of the others and subtends an angle $\ge 120°$.
-/
theorem erdos_problem_99.variants.four_points_counterexample :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 4 ∧ MinimisesDiameter A ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → ¬ IsEquilateralTriangle a b c 1 :=
  sorry
