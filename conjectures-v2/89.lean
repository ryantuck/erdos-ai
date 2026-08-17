import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Finset.Basic

open Real Finset

noncomputable section

/-!
# Erdős Problem #89 — the distinct distances problem

Verbatim from erdosproblems.com/89 (page edition 23 January 2026, archived capture
accessed 2026-03-05):

"Does every set of $n$ distinct points in $\mathbb{R}^2$ determine
$\gg n/\sqrt{\log n}$ many distinct distances?"

**Status: OPEN — $500 prize** (page banner: "This is open, and cannot be resolved
with a finite computation"; confirmed open by the teorth/erdosproblems metadata
mirror, last update 2025-08-31). The main theorem below asserts the affirmative
direction of the open yes/no question with `sorry` — the standard encoding for open
questions in this pipeline (no `answer()` elaborator is available here).

Remarks from the problem page:

* A √n × √n integer grid shows that this would be the best possible
  (`erdos_problem_89.variants.grid_upper_bound` below).
* Nearly solved by Guth and Katz [GuKa15], who proved that there are always
  ≫ n / log n many distinct distances
  (`erdos_problem_89.variants.guth_katz` below).
* A stronger form (see problem [604]) may be true: is there a single point which
  determines ≫ n/√(log n) distinct distances, or even ≫ n many such points, or
  even that this is true averaged over all points — for example, if d(x) counts
  the number of distinct distances from x, then in [Er75f] Erdős conjectured
  Σ_{x ∈ A} d(x) ≫ n²/√(log n) for any set A ⊂ ℝ² of n points
  (`erdos_problem_89.variants.sum_distinct_distances` below; the single-point
  forms are problem 604's own content and are not duplicated here).
* See also problems [661], and [1083] for the generalisation to higher dimensions.

Citation keys on the page: [Er46b], [Er57], [Er61], [Er75f, p.99], [Er81],
[Er82e], [Er83c], [Er85], [Er87b, p.170], [Er90], [Er92e], [Er95], [Er97b],
[Er97c], [Er97e], [Er97f], [Va99, 4.69]; and [GuKa15] in the remarks.

References (honest stubs; the site's /latex/89 bibliography was not recoverable
from the archived material, so full data is given only where it could be
cross-derived from recovered in-repo/upstream sources):

[Er46b] Erdős, P., _On sets of distances of n points_. Amer. Math. Monthly 53
(1946), 248-250. (Title/journal/pages from the recovered reference block in
`conjectures/1084.lean`; volume from the upstream formal-conjectures 89.lean,
which carries the same paper as [Er46]. The two sources agree.)

[GuKa15] Guth, L. and Katz, N. H., _On the Erdős distinct distances problem in
the plane_. Ann. of Math. (2) 181 (2015), 155-190. (From the upstream
formal-conjectures 89.lean and `deepmind/deepmind/95.lean`, which agree.)

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Annali di Matematica Pura ed Applicata (4) (1975), 99-108. (From the recovered
reference block in `conjectures/1084.lean`; consistent with the page's
[Er75f, p.99]. Volume number DEFERRED.)

[Er57], [Er61], [Er81], [Er82e], [Er83c], [Er85], [Er87b], [Er90], [Er92e],
[Er95], [Er97b], [Er97c], [Er97e], [Er97f], [Va99]: key-only stubs — full
bibliographic data DEFERRED (not recoverable offline; sibling files expand some
of these keys inconsistently, so no expansion is imported).

Tags: geometry, distances. Related OEIS sequences: A186704, A131628.

https://www.erdosproblems.com/89
-/

/--
The set of distinct pairwise distances determined by a finite point set in ℝ².

Distances are collected over ordered pairs of *distinct* points and deduplicated
by `Finset.image`, so `(distinctDistances A).card` is exactly the number of
distinct distances: `∅` and singletons give `∅`; two points give a single
distance. (The filtered product `(A ×ˢ A).filter (p.1 ≠ p.2)` coincides with
Mathlib's `Finset.offDiag A`; the explicit form is kept as in the compile-proven
input.)
-/
def distinctDistances (A : Finset (EuclideanSpace ℝ (Fin 2))) : Finset ℝ :=
  (A.product A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => dist p.1 p.2)

/--
The number of distinct distances from the point `x` to the other points of `A`
(the quantity d(x) of the problem page's remarks). For `x ∈ A` the point itself
is removed by `erase`, so the trivial distance 0 is not counted; distinct points
of a metric space are never at distance 0, so no other pair contributes 0.

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
def distinctDistancesFrom (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) : ℕ :=
  ((A.erase x).image (fun y => dist x y)).card

/--
**Erdős Problem #89** (OPEN, $500):

Does every set of n distinct points in ℝ² determine ≫ n/√(log n) many distinct
distances? That is, there exists an absolute constant C > 0 such that every
finite A ⊂ ℝ² determines at least C·|A|/√(log |A|) distinct distances.

Encoding notes. (i) The source is an open yes/no question; the affirmative
direction is asserted, per the pipeline convention for open questions.
(ii) The Vinogradov "≫" is rendered as a single uniform constant over *all* A
(`∃ C, ∀ A`), which is equivalent to the eventual form: for every n ≥ 2 the
minimum number of distinct distances is ≥ 1 while n/√(log n) is finite, so the
finitely many small-n cases only shrink the constant. (iii) Degenerate inputs
are harmless junk-value cases that hold trivially: for |A| = 1, log 1 = 0 and
Lean's x/0 = 0 convention makes the RHS 0; for |A| = 0, Real.log 0 = 0 gives
RHS 0 as well, and the LHS is always ≥ 0.

A √n × √n integer grid shows that this would be best possible. Nearly solved
by Guth and Katz [GuKa15] (2015) who proved that there are always ≫ n / log n
many distinct distances.
-/
theorem erdos_problem_89 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        (distinctDistances A).card ≥ C * A.card / Real.sqrt (Real.log A.card) :=
  sorry

/--
**Erdős Problem #89** — Guth–Katz lower bound (solved, [GuKa15]):

Every set of n points in ℝ² determines ≫ n/log n distinct distances
(Guth and Katz, Ann. of Math. 2015). Uniform-constant encoding as in the main
theorem; the |A| ≤ 1 junk-value cases are again trivially true (log 1 = 0 and
x/0 = 0), and small |A| ≥ 2 cases only shrink the constant.

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
theorem erdos_problem_89.variants.guth_katz :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        ((distinctDistances A).card : ℝ) ≥ C * A.card / Real.log A.card :=
  sorry

/--
**Erdős Problem #89** — grid upper bound (solved, Erdős [Er46b]):

A √n × √n integer grid determines only O(n/√(log n)) distinct distances, so the
conjectured lower bound would be best possible: there is a constant C > 0 such
that for every n there exists an n-point set with at most C·n/√(log n) distinct
distances. (For non-square n, an n-point subset of the ⌈√n⌉ × ⌈√n⌉ grid works;
n ≤ 1 gives 0 ≤ 0 by the junk-value conventions, and the finitely many other
small n only raise the constant.)

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
theorem erdos_problem_89.variants.grid_upper_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
        A.card = n ∧
        ((distinctDistances A).card : ℝ) ≤ C * n / Real.sqrt (Real.log n) :=
  sorry

/--
**Erdős Problem #89** — averaged strong form (OPEN, Erdős [Er75f]; see also
problem 604):

If d(x) counts the number of distinct distances from x to the other points of A,
then Erdős conjectured Σ_{x ∈ A} d(x) ≫ n²/√(log n) for any set A ⊂ ℝ² of n
points. Uniform-constant encoding as in the main theorem; for |A| ≤ 1 both sides
are 0 by the junk-value conventions, and for |A| ≥ 2 the sum is ≥ |A| > 0, so
the finitely many small cases only shrink the constant.

NOTE: added during Fable review from the archived page content; not
compile-verified.
-/
theorem erdos_problem_89.variants.sum_distinct_distances :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Finset (EuclideanSpace ℝ (Fin 2))),
        (∑ x ∈ A, (distinctDistancesFrom A x : ℝ)) ≥
          C * (A.card : ℝ) ^ 2 / Real.sqrt (Real.log A.card) :=
  sorry

end
