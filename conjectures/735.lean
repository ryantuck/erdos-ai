import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #735

Given any n points in ℝ², when can one assign positive weights to the points
such that the sum of the weights along every line containing at least two points
is the same?

A problem of Murty, who conjectured this is only possible in one of four cases:
1. All points on a line
2. No three points on a line (general position)
3. n − 1 points on a line (with one point off)
4. The 7-point incenter configuration: a triangle, the feet of the three angle
   bisectors, and the incenter (or a projective equivalence)

Proved by Ackerman, Buchin, Knauer, Pinchasi, and Rote [ABKPR08].
-/

abbrev R2_735 := EuclideanSpace ℝ (Fin 2)

/-- A finite set of points in ℝ² admits a balanced weighting if there exist positive
    real weights such that the total weight on every line through ≥ 2 points is the same. -/
def AdmitsBalancedWeighting735 (S : Finset R2_735) : Prop :=
  ∃ (w : R2_735 → ℝ),
    (∀ p ∈ S, w p > 0) ∧
    ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ p₂ ∈ S, ∀ q₂ ∈ S,
      p₁ ≠ q₁ → p₂ ≠ q₂ →
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₁, q₁, x} : Set R2_735)), w x =
      ∑ x ∈ S.filter (fun x => Collinear ℝ ({p₂, q₂, x} : Set R2_735)), w x

/-- All points of S are collinear (lie on a single line). -/
def AllCollinear735 (S : Finset R2_735) : Prop :=
  Collinear ℝ (↑S : Set R2_735)

/-- No three points of S are collinear (S is in general position). -/
def NoThreeCollinear735 (S : Finset R2_735) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set R2_735)

/-- All but one point of S are collinear, and the full set is not collinear. -/
def AllButOneCollinear735 (S : Finset R2_735) : Prop :=
  ∃ p ∈ S, Collinear ℝ (↑(S.erase p) : Set R2_735) ∧ ¬Collinear ℝ (↑S : Set R2_735)

/-- The 7-point incenter configuration: vertices A, B, C of a non-degenerate triangle,
    the incenter, and the three feet of the angle bisectors from A, B, C to the
    opposite sides. Here a = |BC|, b = |CA|, c = |AB|. The foot from A to BC
    divides BC in the ratio c : b (by the angle bisector theorem), and similarly
    for the other feet. The full classification includes projective equivalences. -/
def IsIncentreConfiguration735 (S : Finset R2_735) : Prop :=
  ∃ (A B C : R2_735),
    ¬Collinear ℝ ({A, B, C} : Set R2_735) ∧ (
      let a := dist B C
      let b := dist C A
      let c := dist A B
      let bisA := (b / (b + c)) • B + (c / (b + c)) • C
      let bisB := (a / (a + c)) • A + (c / (a + c)) • C
      let bisC := (a / (a + b)) • A + (b / (a + b)) • B
      let inc := (a / (a + b + c)) • A + (b / (a + b + c)) • B + (c / (a + b + c)) • C
      S = ({A, B, C, bisA, bisB, bisC, inc} : Finset R2_735))

/--
Erdős Problem #735 (Murty's conjecture, proved by Ackerman–Buchin–Knauer–Pinchasi–Rote):

A finite set S of at least 2 points in ℝ² admits a balanced weighting if and only if
S is one of:
1. All points collinear,
2. No three points collinear (general position),
3. All but one point collinear, or
4. The 7-point incenter configuration (or a projective equivalence).
-/
theorem erdos_problem_735 (S : Finset R2_735) (hS : 2 ≤ S.card) :
    AdmitsBalancedWeighting735 S ↔
      AllCollinear735 S ∨ NoThreeCollinear735 S ∨ AllButOneCollinear735 S ∨
      IsIncentreConfiguration735 S :=
  sorry

end
