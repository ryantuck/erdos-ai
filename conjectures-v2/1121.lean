import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1121

Source: https://www.erdosproblems.com/1121 (page last edited 30 December 2025;
archived capture accessed 2026-02-23).

Verbatim statement: "If $C_1,\ldots,C_n$ are circles in $\mathbb{R}^2$ with
radii $r_1,\ldots,r_n$ such that no line disjoint from all the circles
divides them into two non-empty sets then the circles can be covered by a
circle of radius $r=\sum r_i$."

Status: PROVED (banner tooltip: "This has been solved in the affirmative.").
Tag: geometry.

Remarks from the page:

* "This was reported as a conjecture of Erdős in [GoGo45]."
* "This is true, and was proved by Goodman and Goodman [GoGo45] (whose proof
  also generalises to higher dimensions)."

Encoding notes. The problem is a direct assertion that has been proved true,
so it is formalized as a bare proposition in the true direction (this raw
corpus has no `answer()` elaborator). Circles are represented by their
centers and positive radii; a line is parameterized by a unit normal $v$ and
offset $d$ as $\{x : \langle x, v\rangle = d\}$ (every line in the plane
arises this way). For unit $v$ the distance from a point $c$ to that line is
$\lvert\langle c, v\rangle - d\rvert$, so the line is disjoint from the
closed disk $\bar B(c, r)$ — equivalently, from the circle bounding it, since
an unbounded connected line meeting the open disk must cross the boundary —
iff $\lvert\langle c, v\rangle - d\rvert > r$; in that case the whole disk
lies strictly on the side of the line containing its center. Hence "no line
disjoint from all the circles divides them into two non-empty sets" is
exactly the hypothesis `hns`: whenever a line is disjoint from every disk,
all centers lie on the same side. "Covered by a circle of radius
$r = \sum r_i$" is encoded as $\exists p,\ \forall i,\
\operatorname{dist}(c_i, p) + r_i \leq \sum_j r_j$, i.e. every closed disk
(equivalently, every circle, whose farthest point from $p$ lies at distance
$\operatorname{dist}(c_i, p) + r_i$) is contained in the single closed ball
$\bar B(p, \sum_j r_j)$.

References (the key [GoGo45] is page-confirmed; no `/latex/1121` or `/bibs/`
fetch is preserved in the session logs, so the journal data below is carried
from the original pipeline's styled file as captured in the
formal-conjectures session logs — consistent with reviewer knowledge of this
well-known paper — and its verification against the site's own bibliography
remains deferred):

[GoGo45] Goodman, A. W. and Goodman, R. E., _A circle covering theorem_,
American Mathematical Monthly 52 (1945), 494-498.

Formalised statement in external databases: No (as of the archived capture).
No related OEIS sequences.
-/

noncomputable section
open scoped BigOperators
open Classical

namespace Erdos1121

/--
Erdős Problem #1121 (proved by Goodman and Goodman [GoGo45]):

If C₁, ..., Cₙ are circles in ℝ² with radii r₁, ..., rₙ such that no line
disjoint from all the circles divides them into two non-empty sets, then the
circles can be covered by a circle of radius r = ∑ rᵢ.

A line in ℝ² is parameterized by a unit normal vector v and offset d, defining
ℓ = {x : ⟨x, v⟩ = d}. The closed disk B̄(cᵢ, rᵢ) is disjoint from ℓ when
|⟨cᵢ, v⟩ − d| > rᵢ. The non-separability condition says that whenever all
disks are disjoint from a line, they all lie on the same side.
-/
theorem erdos_problem_1121
    (n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin 2))
    (radius : Fin n → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin 2)) (d : ℝ),
      ‖v‖ = 1 →
      (∀ i, |@inner ℝ _ _ (center i) v - d| > radius i) →
      (∀ i j, @inner ℝ _ _ (center i) v > d ↔ @inner ℝ _ _ (center j) v > d)) :
    ∃ p : EuclideanSpace ℝ (Fin 2),
      ∀ i, dist (center i) p + radius i ≤ ∑ j : Fin n, radius j :=
  sorry

/--
Higher-dimensional generalization (page-confirmed remark: the result "was
proved by Goodman and Goodman [GoGo45] (whose proof also generalises to
higher dimensions)"): if closed balls B̄(cᵢ, rᵢ) in ℝᵐ are such that no
hyperplane disjoint from all of them separates them into two non-empty sets,
then they can be covered by a single ball of radius ∑ rᵢ.

Hyperplanes in ℝᵐ are parameterized by a unit normal v and offset d exactly
as lines are in the m = 2 case. The degenerate dimensions are harmless: for
m = 0 no unit vector exists, so `hns` is vacuous, and the one-point space
satisfies the conclusion since each rᵢ ≤ ∑ⱼ rⱼ; for m = 1 the "hyperplanes"
are points and the statement is the (true) interval version.

NOTE: added from the recovered source page; not compile-verified.
-/
theorem erdos_problem_1121.variants.higher_dimensions
    (m n : ℕ)
    (center : Fin n → EuclideanSpace ℝ (Fin m))
    (radius : Fin n → ℝ)
    (hr : ∀ i, 0 < radius i)
    (hns : ∀ (v : EuclideanSpace ℝ (Fin m)) (d : ℝ),
      ‖v‖ = 1 →
      (∀ i, |@inner ℝ _ _ (center i) v - d| > radius i) →
      (∀ i j, @inner ℝ _ _ (center i) v > d ↔ @inner ℝ _ _ (center j) v > d)) :
    ∃ p : EuclideanSpace ℝ (Fin m),
      ∀ i, dist (center i) p + radius i ≤ ∑ j : Fin n, radius j :=
  sorry

end Erdos1121
