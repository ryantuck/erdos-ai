-- [AI - Claude Opus 5.5]: Erdős Problem 100 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #100

*Source:* [erdosproblems.com/100](https://www.erdosproblems.com/100) (status **OPEN**: "This
is open, and cannot be resolved with a finite computation."; captured 2026-02-19 and
2026-03-05 as the tidied problem box, with no page-edit date). [Er90] [Er92e] [Er95] [Er97f]

Let $A$ be a set of $n$ points in $\mathbb{R}^2$ such that all pairwise distances are at least
$1$ and if two distinct distances differ then they differ by at least $1$. Is the diameter of
$A$ $\gg n$?

Remarks recorded on the page:
* Perhaps the diameter is even $\ge n - 1$ for sufficiently large $n$.
* Piepmeyer has an example of $9$ such points with diameter $< 5$.
* Kanold proved the diameter is $\ge n^{3/4}$.
* The bounds on the distinct distance problem (#89) proved by Guth and Katz [GuKa15] imply a
  lower bound of $\gg n / \log n$.

**Encoding.** "Diameter $\gg n$" means $\operatorname{diam} A \ge C n$ for some absolute
$C > 0$ and all admissible $A$ with $n \ge 2$ points. For $n \le 1$ the diameter is $0$, so
those sets must be excluded. Below two points `diameter'` returns the junk value `0`, which
agrees with `Metric.diam`.

Tags: geometry, distances.

## References

* [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul Erdős
  (1990), 467–478.
* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and probability
  (Cambridge, 1993) (1997), 1–10.
* [GuKa15] Guth, L. and Katz, N. H., _On the Erdős distinct distances problem in the plane_.
  Ann. of Math. (2) (2015), 155–190.
* Kanold's and Piepmeyer's results carry no reference on the page. Upstream
  formal-conjectures also records "No references found".

(Provenance: the original pipeline's `/latex` extractions for sibling problems: 91 for [Er90],
94 for [Er92e], 75/843 for [Er95], several for [Er97f], and 95 for [GuKa15].)
-/

/--
The diameter of a finite set of points (maximum pairwise distance), or the junk value `0` if
the set has fewer than two points, which agrees with `Metric.diam`. (The first-pass version
discharged the nonemptiness obligation with `sorry`; this one is total.)
-/
def diameter' (A : Finset (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  if h : (A.offDiag.image (fun p => dist p.1 p.2)).Nonempty then
    (A.offDiag.image (fun p => dist p.1 p.2)).max' h
  else 0

/--
All pairwise distances are at least 1.
-/
def allPairwiseDistAtLeastOne (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → dist a b ≥ 1

/--
Any two distinct pairwise distances differ by at least 1.
-/
def distinctDistancesDifferByAtLeastOne (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a ≠ b → c ≠ d → dist a b ≠ dist c d → |dist a b - dist c d| ≥ 1

/--
Erdős Problem #100 [Er90, Er92e, Er95, Er97f] (OPEN):

Let A be a set of n points in ℝ² such that all pairwise distances are at least 1
and if two distinct pairwise distances differ then they differ by at least 1.
Is the diameter of A ≫ n?

That is, there exists an absolute constant C > 0 such that for all such sets A
with at least two points, the diameter is at least C · |A|. The hypothesis `2 ≤ A.card` is
necessary: a one-point set satisfies both conditions vacuously and has diameter `0 < C`.

Kanold proved the diameter is ≫ n^(3/4). The Guth–Katz distinct distances bound
implies a lower bound of ≫ n / log n. Erdős conjectured the diameter may even be
≥ n − 1 for sufficiently large n.
-/
theorem erdos_problem_100 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        2 ≤ A.card →
        allPairwiseDistAtLeastOne A →
        distinctDistancesDifferByAtLeastOne A →
        diameter' A ≥ C * A.card :=
  sorry

/--
Erdős's stronger guess (OPEN): perhaps the diameter is $\ge n - 1$ for all large $n$. Points
$0, 1, \ldots, n-1$ on a line show that $n - 1$ would be sharp.
-/
theorem erdos_problem_100.variants.n_minus_one :
    ∃ N : ℕ, ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
      N ≤ A.card →
      allPairwiseDistAtLeastOne A →
      distinctDistancesDifferByAtLeastOne A →
      diameter' A ≥ (A.card : ℝ) - 1 :=
  sorry

/--
Piepmeyer (PROVED): there are 9 such points with diameter $< 5$. So $n - 1$ fails at
$n = 9$, which is why the guess above is only for large $n$.
-/
theorem erdos_problem_100.variants.piepmeyer :
    ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.card = 9 ∧ allPairwiseDistAtLeastOne A ∧ distinctDistancesDifferByAtLeastOne A ∧
      diameter' A < 5 :=
  sorry

/--
Kanold (PROVED): the diameter is $\gg n^{3/4}$. The page writes "$\ge n^{3/4}$", but read
literally for every $n$ that is false: two points at distance 1 have diameter
$1 < 2^{3/4} \approx 1.68$. So a constant is included.
-/
theorem erdos_problem_100.variants.kanold :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        2 ≤ A.card →
        allPairwiseDistAtLeastOne A →
        distinctDistancesDifferByAtLeastOne A →
        diameter' A ≥ c * (A.card : ℝ) ^ ((3 : ℝ) / 4) :=
  sorry

/--
Via Guth–Katz [GuKa15] (PROVED): the diameter is $\gg n / \log n$. The $k$ distinct distances
are $\ge 1$ and pairwise $\ge 1$ apart, so the largest is $\ge k$, and Guth–Katz gives
$k \gg n / \log n$.
-/
theorem erdos_problem_100.variants.guth_katz :
    ∃ c : ℝ, 0 < c ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        2 ≤ A.card →
        allPairwiseDistAtLeastOne A →
        distinctDistancesDifferByAtLeastOne A →
        diameter' A ≥ c * (A.card : ℝ) / Real.log (A.card : ℝ) :=
  sorry

end
