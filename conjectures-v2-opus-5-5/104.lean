-- [AI - Claude Opus 5.5]: Erdős Problem 104 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

/-!
# Erdős Problem #104

*Source:* [erdosproblems.com/104](https://www.erdosproblems.com/104) (status **OPEN**, \$100:
"This is open, and cannot be resolved with a finite computation."; captured 2026-02-19 as the
tidied problem box). [Er75h, p.2] [Er81d, p.144] [Er83b] [Er92e, p.46] [Er95, p.182]

Given $n$ points in $\mathbb{R}^2$ the number of distinct unit circles containing at least
three points is $o(n^2)$.

Remarks recorded on the page:
* In [Er81d] Erdős proved that $\gg n$ such circles are possible and that there cannot be more
  than $O(n^2)$. Every pair of points determines at most $2$ unit circles, so double counting
  gives the bound. Erdős claimed this gives $n(n-1)$, but Harborth and Mengersen [HaMe86] note
  that it in fact gives $\frac{n(n-1)}{3}$. (The page's remark spells the name "Mengerson";
  its bibliography has Mengersen.)
* Elekes [El84] has a simple construction with $\gg n^{3/2}$ such circles. This may be the
  correct order of magnitude.
* In [Er75h] and [Er92e] Erdős also asks how many such unit circles there must be if the
  points are in general position.
* In [Er92e] Erdős offered £100 for a proof or disproof that the answer is $O(n^{3/2})$.
* The maximal number of unit circles achieved by $n$ points is OEIS A003829. See also
  Problems #506 and #831.

**Encoding.** A unit circle is identified with its centre. "Containing" a point means the
point lies on the circle. The set of qualifying centres is finite: each is a centre of a unit
circle through two of the points, and two points determine at most two such centres. So
`Set.ncard` is its true size.

Tags: geometry. OEIS: A003829.

## References

* [Er75h] Erdős, P., _Some problems on elementary geometry_. Austral. Math. Soc. Gaz. (1975),
  2–3.
* [Er81d] Erdős, P., _Some applications of graph theory and combinatorial methods to number
  theory and geometry_. Algebraic methods in graph theory, Vol. I, II (Szeged, 1978) (1981),
  137–148.
* [Er83b] Erdős, P. (1983). Stub: not recovered.
* [Er92e] Erdős, P., _Some unsolved problems in geometry, number theory and combinatorics_.
  Eureka (1992), 44–48.
* [Er95] Erdős, P., _Some of my favourite problems in number theory, combinatorics, and
  geometry_. Resenhas (1995), 165–186.
* [HaMe86] Harborth, H. and Mengersen, I., _Point sets with many unit circles_. Discrete Math.
  (1986), 193–197.
* [El84] Elekes, G., _$n$ points in the plane can determine $n^{3/2}$ unit circles_.
  Combinatorica (1984), 131.

(Provenance: the original pipeline's fetch of `erdosproblems.com/latex/104` for [Er75h],
[Er81d], [HaMe86] and [El84]. [Er92e] and [Er95] come from sibling extractions. These agree
with upstream formal-conjectures at `df3f12d`, which also omits [Er83b].)
-/

/--
The number of distinct unit circles in ℝ² that contain at least three points
from P. A unit circle is uniquely determined by its center (since the radius
is fixed at 1), so two unit circles are distinct iff they have different centers.
-/
noncomputable def threeRichUnitCircleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  Set.ncard {c : EuclideanSpace ℝ (Fin 2) |
    3 ≤ Set.ncard {p : EuclideanSpace ℝ (Fin 2) | p ∈ (P : Set _) ∧ dist p c = 1}}

/--
Erdős Problem #104 (OPEN, \$100):
Given n points in ℝ², the number of distinct unit circles containing at least
three points is o(n²).

Formally: for every ε > 0 there exists N such that for all n ≥ N and every
set P of n points in ℝ², the number of unit circles (of radius 1) that each
contain at least 3 points of P is at most ε · n².
-/
theorem erdos_problem_104 :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        (threeRichUnitCircleCount P : ℝ) ≤ ε * (n : ℝ) ^ 2 :=
  sorry

/--
Harborth and Mengersen [HaMe86] (PROVED, by double counting): at most $\frac{n(n-1)}{3}$
qualifying unit circles. Each pair of points lies on at most 2 unit circles, and each
qualifying circle contains at least $\binom32 = 3$ pairs.
-/
theorem erdos_problem_104.variants.harborth_mengersen (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    3 * threeRichUnitCircleCount P ≤ P.card * (P.card - 1) :=
  sorry

/--
Elekes [El84] (PROVED): configurations with $\gg n^{3/2}$ qualifying unit circles exist.
Stated for arbitrarily large `n`.
-/
theorem erdos_problem_104.variants.elekes :
    ∃ c : ℝ, c > 0 ∧ ∃ᶠ n : ℕ in atTop,
      ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n ∧ c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (threeRichUnitCircleCount P : ℝ) :=
  sorry

/--
Erdős's £100 question [Er92e] (OPEN; he offered the prize for a proof *or* a disproof): is the
number of qualifying unit circles $O(n^{3/2})$? This is the positive form. With
`variants.elekes` it would make $n^{3/2}$ the true order.
-/
theorem erdos_problem_104.variants.three_halves :
    ∃ C : ℝ, C > 0 ∧ ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      (threeRichUnitCircleCount P : ℝ) ≤ C * (P.card : ℝ) ^ ((3 : ℝ) / 2) :=
  sorry
