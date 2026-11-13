-- [AI - Claude Fable 5.2]: Erdős Problem 209 — second-pass formalization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem #209

*Source:* [erdosproblems.com/209](https://www.erdosproblems.com/209) (status **DISPROVED**: "This
has been solved in the negative."; captured 2026-02-20). [Er84] [ErPu95b]

Let $A$ be a finite collection of $d\geq 4$ non-parallel lines in $\mathbb{R}^2$ such that there
are no points where at least four lines from $A$ meet. Must there exist a 'Gallai triangle' (or
'ordinary triangle'): three lines from $A$ which intersect in three points, and each of these
intersection points only intersects two lines from $A$?

Remarks recorded on the page: equivalently, one can ask the dual problem: given $n$ points in
$\mathbb{R}^2$ such that there are no lines containing at least four points then there are three
points such that the lines determined by them are ordinary ones (i.e. contain exactly two points
each). The Sylvester-Gallai theorem implies that there must exist a point where only two lines
from $A$ meet. This problem asks whether there must exist three such points which form a triangle
(with sides induced by lines from $A$). Füredi and Palásti [FuPa84] showed this is false when
$d\geq 4$ is not divisible by $9$. Escudero [Es16] showed this is false for all $d\geq 4$. See also
[960].

## Status after capture

The metadata mirror `teorth/erdosproblems` (`641a78e`, 2026-11-12) lists the problem as
**disproved (Lean)** since 2026-06-21. Upstream `formal-conjectures` (`5258ab9`) states the negative
answer in the weak form `¬ ∀ d ≥ 4, ∀ A, … → HasGallaiTriangle A`, with a linked Lean proof. The
main theorem below is the stronger statement the page attributes to Escudero [Es16] (a
counterexample for *every* `d ≥ 4`); [Es16] was not read in this review, and the linked Lean proof
is of the weak form only.

## Encoding notes

* The theorem asserts, for every `d ≥ 4`, an arrangement of `d` pairwise non-parallel lines with
  at most three through any point and no Gallai triangle. It implies the negative answer to the
  question as asked (`erdos_problem_209.question_false_of_main`, PROVED in Lean), and it contains
  the Füredi–Palásti statement.
* `IsLine` is "direction of dimension one", so `⊥` and `⊤` are not lines (`not_isLine_bot`,
  `not_isLine_top`, PROVED in Lean).
* Two distinct lines meet in at most one point (`eq_of_mem_of_mem`, PROVED in Lean), so the three
  points of `HasGallaiTriangle` are *the* intersection points of the three lines.
* For `d = 4` the statement is elementary: three concurrent lines and a fourth line through none
  of their common point have every triangle through the triple point (argued in the review, not
  proved in Lean).
* The dual (points and ordinary lines) formulation on the page is not formalized.

## References

From the site's `/latex/209` bibliography:
* [Es16] Escudero, Juan García, _Gallai triangles in configurations of lines in the projective
  plane_. C. R. Math. Acad. Sci. Paris (2016), 551–554.
* [FuPa84] Füredi, Z. and Palásti, I., _Arrangements of lines with a large number of triangles_.
  Proc. Amer. Math. Soc. (1984), 561–566.

Not in `/latex/209`:
* [Er84] Erdős, P., _Research problems_. Period. Math. Hungar. (1984), 101–103. (Site
  `/latex/211`.)
* [ErPu95b] Erdős, Paul and Purdy, George, _Extremal problems in combinatorial geometry_. Handbook
  of combinatorics, Vol. 1, 2 (1995), 809–874. (**DEFERRED:** from upstream's Problem 209 file; no
  site entry was recovered.)

*Provenance:* second pass of `conjectures/209.lean` (Fable 5.2 review,
`fable-5-2-review/209.md`).
-/

noncomputable section
open Classical

/-- Points in the Euclidean plane ℝ² -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- An affine subspace of ℝ² is a line if it has dimension 1 -/
def IsLine (L : AffineSubspace ℝ Point2) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- Two affine subspaces are parallel if they have the same direction -/
def AreParallel (L₁ L₂ : AffineSubspace ℝ Point2) : Prop :=
  L₁.direction = L₂.direction

/-- The number of lines from A passing through a point p -/
def pointMultiplicity (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : ℕ :=
  (A.filter (fun L => (p : Point2) ∈ L)).card

/-- A point is ordinary if exactly 2 lines from A pass through it -/
def IsOrdinaryPoint (A : Finset (AffineSubspace ℝ Point2)) (p : Point2) : Prop :=
  pointMultiplicity A p = 2

/-- A Gallai (ordinary) triangle: three lines forming a triangle with
    all three vertices being ordinary points -/
def HasGallaiTriangle (A : Finset (AffineSubspace ℝ Point2)) : Prop :=
  ∃ L₁ ∈ A, ∃ L₂ ∈ A, ∃ L₃ ∈ A,
    L₁ ≠ L₂ ∧ L₂ ≠ L₃ ∧ L₁ ≠ L₃ ∧
    ∃ p₁₂ p₂₃ p₁₃ : Point2,
      (p₁₂ : Point2) ∈ L₁ ∧ (p₁₂ : Point2) ∈ L₂ ∧
      (p₂₃ : Point2) ∈ L₂ ∧ (p₂₃ : Point2) ∈ L₃ ∧
      (p₁₃ : Point2) ∈ L₁ ∧ (p₁₃ : Point2) ∈ L₃ ∧
      p₁₂ ≠ p₂₃ ∧ p₂₃ ≠ p₁₃ ∧ p₁₂ ≠ p₁₃ ∧
      IsOrdinaryPoint A p₁₂ ∧ IsOrdinaryPoint A p₂₃ ∧ IsOrdinaryPoint A p₁₃

/--
Erdős Problem #209 (Disproved) [Er84, ErPu95b]:
Let A be a finite collection of d ≥ 4 non-parallel lines in ℝ² such that no
point has 4 or more lines from A passing through it. The question asked whether
there must exist a 'Gallai triangle' (ordinary triangle): three lines from A
which intersect in three points, each being an ordinary point (exactly two lines
from A meet there).

Disproved by Füredi-Palásti [FuPa84] for d not divisible by 9, and by Escudero [Es16] for all
d ≥ 4. The statement is Escudero's: a counterexample for every d ≥ 4. Not proved here.
-/
theorem erdos_problem_209 :
    ∀ d : ℕ, d ≥ 4 →
      ∃ A : Finset (AffineSubspace ℝ Point2),
        A.card = d ∧
        (∀ L ∈ A, IsLine L) ∧
        (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
        (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
        ¬HasGallaiTriangle A :=
  sorry

/-- The main statement implies the negative answer to the question as asked (PROVED in Lean): it
is not true that every admissible arrangement of `d ≥ 4` lines has a Gallai triangle. Only the case
`d = 4` of the main statement is used. -/
theorem erdos_problem_209.question_false_of_main
    (h : ∀ d : ℕ, d ≥ 4 →
      ∃ A : Finset (AffineSubspace ℝ Point2),
        A.card = d ∧
        (∀ L ∈ A, IsLine L) ∧
        (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
        (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
        ¬HasGallaiTriangle A) :
    ¬ ∀ d : ℕ, d ≥ 4 → ∀ A : Finset (AffineSubspace ℝ Point2),
      A.card = d →
      (∀ L ∈ A, IsLine L) →
      (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) →
      (∀ p : Point2, pointMultiplicity A p ≤ 3) →
      HasGallaiTriangle A := by
  intro hall
  obtain ⟨A, hcard, hline, hpar, hmult, hno⟩ := h 4 (le_refl 4)
  exact hno (hall 4 (le_refl 4) A hcard hline hpar hmult)

/-- The empty affine subspace is not a line (PROVED in Lean). -/
theorem erdos_problem_209.not_isLine_bot : ¬IsLine (⊥ : AffineSubspace ℝ Point2) := by
  unfold IsLine
  rw [AffineSubspace.direction_bot, finrank_bot]
  norm_num

/-- The whole plane is not a line (PROVED in Lean). -/
theorem erdos_problem_209.not_isLine_top : ¬IsLine (⊤ : AffineSubspace ℝ Point2) := by
  unfold IsLine
  rw [AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin]
  norm_num

/-- Two distinct lines meet in at most one point (PROVED in Lean). Hence the points `p₁₂`, `p₂₃`,
`p₁₃` in `HasGallaiTriangle` are the intersection points of the three lines. -/
theorem erdos_problem_209.eq_of_mem_of_mem {L₁ L₂ : AffineSubspace ℝ Point2} (h₁ : IsLine L₁)
    (h₂ : IsLine L₂) (hne : L₁ ≠ L₂) {p q : Point2} (hp₁ : p ∈ L₁) (hp₂ : p ∈ L₂)
    (hq₁ : q ∈ L₁) (hq₂ : q ∈ L₂) : p = q := by
  by_contra hpq
  apply hne
  have hv0 : q -ᵥ p ≠ (0 : Point2) := by
    rw [Ne, vsub_eq_zero_iff_eq]
    exact fun h => hpq h.symm
  have hv₁ : q -ᵥ p ∈ L₁.direction := AffineSubspace.vsub_mem_direction hq₁ hp₁
  have hv₂ : q -ᵥ p ∈ L₂.direction := AffineSubspace.vsub_mem_direction hq₂ hp₂
  have hspan : Module.finrank ℝ (Submodule.span ℝ ({q -ᵥ p} : Set Point2)) = 1 :=
    finrank_span_singleton hv0
  have e₁ : Submodule.span ℝ ({q -ᵥ p} : Set Point2) = L₁.direction :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2 hv₁) (hspan.trans h₁.symm)
  have e₂ : Submodule.span ℝ ({q -ᵥ p} : Set Point2) = L₂.direction :=
    Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2 hv₂) (hspan.trans h₂.symm)
  exact AffineSubspace.ext_of_direction_eq (e₁.symm.trans e₂) ⟨p, hp₁, hp₂⟩

/-- A Gallai triangle uses three lines, so an arrangement with a Gallai triangle has at least
three lines (PROVED in Lean). -/
theorem erdos_problem_209.three_le_card_of_hasGallaiTriangle
    {A : Finset (AffineSubspace ℝ Point2)} (h : HasGallaiTriangle A) : 3 ≤ A.card := by
  obtain ⟨L₁, h₁, L₂, h₂, L₃, h₃, h12, h23, h13, -⟩ := h
  have hsub : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ Point2)) ⊆ A := by
    intro L hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl <;> assumption
  have hcard : ({L₁, L₂, L₃} : Finset (AffineSubspace ℝ Point2)).card = 3 :=
    Finset.card_eq_three.2 ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩
  have := Finset.card_le_card hsub
  omega

/-- Füredi and Palásti [FuPa84] (SOLVED; not proved here): a counterexample for every `d ≥ 4` not
divisible by `9`. This is a special case of the main statement. -/
theorem erdos_problem_209.variants.furedi_palasti :
    ∀ d : ℕ, d ≥ 4 → ¬ 9 ∣ d →
      ∃ A : Finset (AffineSubspace ℝ Point2),
        A.card = d ∧
        (∀ L ∈ A, IsLine L) ∧
        (∀ L₁ ∈ A, ∀ L₂ ∈ A, L₁ ≠ L₂ → ¬AreParallel L₁ L₂) ∧
        (∀ p : Point2, pointMultiplicity A p ≤ 3) ∧
        ¬HasGallaiTriangle A :=
  sorry

end
