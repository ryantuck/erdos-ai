-- [AI - Claude Opus 5.5]: Erdős Problem 173 — second-pass formalization
import Mathlib.Data.Real.Basic
import Mathlib.Data.Multiset.Basic

import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

/-!
# Erdős Problem #173

*Source:* [erdosproblems.com/173](https://www.erdosproblems.com/173) (status **OPEN**: "This is open,
and cannot be resolved with a finite computation."; captured 2026-02-20; page edited 16 October
2025). [Er75f, p.108] [ErGr79] [ErGr80] [Er83c]

In any $2$-colouring of $\mathbb{R}^2$, for all but at most one triangle $T$, there is a
monochromatic congruent copy of $T$.

Remarks recorded on the page: for some colourings a single equilateral triangle has to be
excluded, considering the colouring by alternating strips. Shader [Sh76] has proved this is true if
we just consider a single right-angled triangle.

## Encoding notes

* Triangles are non-degenerate triples in `ℝ × ℝ` (with the Euclidean distance written out, since
  Mathlib's metric on `ℝ × ℝ` is the sup metric). Congruence is equality of the multisets of squared
  side lengths (SSS). "All but at most one triangle" is stated as: two triangles that both have no
  monochromatic congruent copy are congruent.
* Checks (PROVED in Lean): `4 · cross² = (∑ sides)² - 2 ∑ sides²` (Heron's formula in squared side
  lengths, `four_mul_cross_sq`), so a congruent copy of a non-degenerate triangle is non-degenerate
  (`nonDegenerate_iff_of_sideSqs_eq`); and the multiset does not depend on the vertex labelling
  (`sideSqs_swap₁₂`).
* The statement is the open conjecture, asserted.

## References

* [Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat. Pura
  Appl. (4) (1975), 99–108. (Site `/latex/1090` and others.)
* [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory_. Monographies de L'Enseignement Mathematique (1980). (Site `/latex/473` and others.)
* [Er83c] Erdős, P., _Combinatorial problems in geometry_. Math. Chronicle (1983), 35–54. (Site
  `/latex/217`.)
* [Sh76] Shader, L., _All right triangles are Ramsey in $\mathbb{R}^2$!_. J. Combin. Theory Ser. A
  (1976), 385–389. (Site `/latex/173`.)
* [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
  theory: van der Waerden's theorem and related topics_. Enseign. Math. (1979), 325–344.
  (**DEFERRED:** from upstream's docstring for Problem 171; no site entry was recovered.)

*Provenance:* second pass of `conjectures/173.lean` (Opus 5.5 review, `opus-5-5-review/173.md`).
-/

/-- Squared Euclidean distance between two points in ℝ². -/
def euclideanDistSq (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The multiset of squared side lengths of a triangle. Two triangles are congruent
    (by SSS) iff their squared side length multisets are equal. -/
def triangleSideSqs (p₁ p₂ p₃ : ℝ × ℝ) : Multiset ℝ :=
  ↑[euclideanDistSq p₁ p₂, euclideanDistSq p₂ p₃, euclideanDistSq p₁ p₃]

/-- A triangle is non-degenerate if its vertices are not collinear. -/
def triangleNonDegenerate (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  (p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2) ≠ 0

/--
Erdős Conjecture (Problem #173) [Er75f, ErGr79, ErGr80, Er83c]:

In any 2-colouring of ℝ², for all but at most one triangle T (up to congruence),
there is a monochromatic congruent copy of T.

Equivalently: if two non-degenerate triangles both fail to have any monochromatic
congruent copy under some 2-colouring, then they must be congruent. (Status: OPEN.)
-/
theorem erdos_problem_173 :
    ∀ f : ℝ × ℝ → Bool,
    ∀ p₁ p₂ p₃ q₁ q₂ q₃ : ℝ × ℝ,
    triangleNonDegenerate p₁ p₂ p₃ →
    triangleNonDegenerate q₁ q₂ q₃ →
    (∀ a₁ a₂ a₃ : ℝ × ℝ, triangleSideSqs a₁ a₂ a₃ = triangleSideSqs p₁ p₂ p₃ →
      ¬(f a₁ = f a₂ ∧ f a₂ = f a₃)) →
    (∀ b₁ b₂ b₃ : ℝ × ℝ, triangleSideSqs b₁ b₂ b₃ = triangleSideSqs q₁ q₂ q₃ →
      ¬(f b₁ = f b₂ ∧ f b₂ = f b₃)) →
    triangleSideSqs p₁ p₂ p₃ = triangleSideSqs q₁ q₂ q₃ :=
  sorry

/-- Heron's formula in squared side lengths (PROVED in Lean): four times the squared cross product
is `(∑ sides)² - 2 ∑ sides²`, a function of the multiset `triangleSideSqs`. -/
theorem erdos_problem_173.four_mul_cross_sq (p₁ p₂ p₃ : ℝ × ℝ) :
    4 * ((p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2)) ^ 2 =
      (triangleSideSqs p₁ p₂ p₃).sum ^ 2 - 2 * ((triangleSideSqs p₁ p₂ p₃).map (· ^ 2)).sum := by
  simp only [triangleSideSqs, Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, euclideanDistSq]
  ring

/-- A congruent copy of a non-degenerate triangle is non-degenerate (PROVED in Lean). -/
theorem erdos_problem_173.nonDegenerate_iff_of_sideSqs_eq {a₁ a₂ a₃ p₁ p₂ p₃ : ℝ × ℝ}
    (h : triangleSideSqs a₁ a₂ a₃ = triangleSideSqs p₁ p₂ p₃) :
    triangleNonDegenerate a₁ a₂ a₃ ↔ triangleNonDegenerate p₁ p₂ p₃ := by
  have key : ∀ q₁ q₂ q₃ : ℝ × ℝ, triangleNonDegenerate q₁ q₂ q₃ ↔
      (triangleSideSqs q₁ q₂ q₃).sum ^ 2 - 2 * ((triangleSideSqs q₁ q₂ q₃).map (· ^ 2)).sum ≠ 0 := by
    intro q₁ q₂ q₃
    rw [← erdos_problem_173.four_mul_cross_sq, triangleNonDegenerate]
    constructor
    · intro hq h0
      apply hq
      have : ((q₂.1 - q₁.1) * (q₃.2 - q₁.2) - (q₃.1 - q₁.1) * (q₂.2 - q₁.2)) ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    · intro hq h0
      apply hq
      rw [h0]; ring
  rw [key, key, h]

/-- The vertex labelling does not matter: swapping two vertices gives the same multiset (PROVED in
Lean). -/
theorem erdos_problem_173.sideSqs_swap₁₂ (p₁ p₂ p₃ : ℝ × ℝ) :
    triangleSideSqs p₂ p₁ p₃ = triangleSideSqs p₁ p₂ p₃ := by
  have h12 : euclideanDistSq p₂ p₁ = euclideanDistSq p₁ p₂ := by
    unfold euclideanDistSq; ring
  simp only [triangleSideSqs, h12]
  exact Multiset.coe_eq_coe.mpr (List.Perm.cons _ (List.Perm.swap _ _ []))

/-- The exception can occur (SOLVED, the page's remark; not proved here): for the colouring by
alternating half-open strips of width `√3/2`, the unit equilateral triangle has no monochromatic
congruent copy. Stated as the existence of such a colouring and an equilateral triangle. -/
theorem erdos_problem_173.variants.equilateral_excluded :
    ∃ f : ℝ × ℝ → Bool, ∃ p₁ p₂ p₃ : ℝ × ℝ,
      triangleNonDegenerate p₁ p₂ p₃ ∧
      euclideanDistSq p₁ p₂ = euclideanDistSq p₂ p₃ ∧
      euclideanDistSq p₂ p₃ = euclideanDistSq p₁ p₃ ∧
      ∀ a₁ a₂ a₃ : ℝ × ℝ, triangleSideSqs a₁ a₂ a₃ = triangleSideSqs p₁ p₂ p₃ →
        ¬(f a₁ = f a₂ ∧ f a₂ = f a₃) :=
  sorry

/-- Shader [Sh76] (SOLVED; not proved here): in any `2`-colouring of the plane, every right
triangle has a monochromatic congruent copy. -/
theorem erdos_problem_173.variants.shader :
    ∀ f : ℝ × ℝ → Bool,
    ∀ p₁ p₂ p₃ : ℝ × ℝ,
    triangleNonDegenerate p₁ p₂ p₃ →
    (p₂.1 - p₁.1) * (p₃.1 - p₁.1) + (p₂.2 - p₁.2) * (p₃.2 - p₁.2) = 0 →
    ∃ a₁ a₂ a₃ : ℝ × ℝ, triangleSideSqs a₁ a₂ a₃ = triangleSideSqs p₁ p₂ p₃ ∧
      f a₁ = f a₂ ∧ f a₂ = f a₃ :=
  sorry

end
