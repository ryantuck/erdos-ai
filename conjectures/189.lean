import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

/--
Four points A, B, C, D in ℝ² form a (nondegenerate) rectangle if:
- ABCD is a parallelogram: C = B + D - A,
- adjacent sides are perpendicular: (B - A) · (D - A) = 0,
- and the rectangle is nondegenerate: A ≠ B and A ≠ D.
-/
def IsRectangle (A B C D : ℝ × ℝ) : Prop :=
  C = (B.1 + D.1 - A.1, B.2 + D.2 - A.2) ∧
  (B.1 - A.1) * (D.1 - A.1) + (B.2 - A.2) * (D.2 - A.2) = 0 ∧
  A ≠ B ∧ A ≠ D

/--
The area of a rectangle with vertex A and adjacent vertices B, D
(where AB ⊥ AD) is the absolute value of the cross product of the
two edge vectors, |AB × AD| = |(B₁-A₁)(D₂-A₂) - (B₂-A₂)(D₁-A₁)|.
-/
noncomputable def RectangleArea (A B D : ℝ × ℝ) : ℝ :=
  |(B.1 - A.1) * (D.2 - A.2) - (B.2 - A.2) * (D.1 - A.1)|

/--
Erdős Problem #189 [ErGr79, ErGr80]:

If ℝ² is finitely coloured then must there exist some colour class which
contains the vertices of a rectangle of every area?

Graham [Gr80] showed this is true with "rectangle" replaced by
"right-angled triangle". The same question can be asked for parallelograms.
It is not true for rhombuses.

This conjecture is false: Kovač [Ko23] provides an explicit colouring using
25 colours such that no colour class contains the vertices of a rectangle
of area 1.
-/
theorem erdos_problem_189 :
    ∀ (k : ℕ) (f : ℝ × ℝ → Fin k),
      ∃ c : Fin k, ∀ t : ℝ, 0 < t →
        ∃ A B C D : ℝ × ℝ,
          f A = c ∧ f B = c ∧ f C = c ∧ f D = c ∧
          IsRectangle A B C D ∧
          RectangleArea A B D = t :=
  sorry
