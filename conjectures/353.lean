import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

noncomputable section

/-- Squared Euclidean distance between two points in ℝ². -/
def sqDist353 (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Area of a triangle with vertices p₁, p₂, p₃ via the cross product formula. -/
def triangleArea353 (p₁ p₂ p₃ : ℝ × ℝ) : ℝ :=
  |(p₂.1 - p₁.1) * (p₃.2 - p₁.2) - (p₃.1 - p₁.1) * (p₂.2 - p₁.2)| / 2

/-- Area of a quadrilateral with consecutive vertices p₁, p₂, p₃, p₄ via the
    shoelace formula. -/
def quadArea353 (p₁ p₂ p₃ p₄ : ℝ × ℝ) : ℝ :=
  |(p₁.1 * p₂.2 - p₂.1 * p₁.2 + p₂.1 * p₃.2 - p₃.1 * p₂.2 +
    p₃.1 * p₄.2 - p₄.1 * p₃.2 + p₄.1 * p₁.2 - p₁.1 * p₄.2)| / 2

/-- Two vectors in ℝ² are parallel (cross product is zero). -/
def Parallel353 (v w : ℝ × ℝ) : Prop :=
  v.1 * w.2 = v.2 * w.1

/-- Three points form an isosceles triangle: all distinct with at least two sides
    of equal length. -/
def IsIsoscelesTriangle353 (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
  (sqDist353 p₁ p₂ = sqDist353 p₁ p₃ ∨
   sqDist353 p₁ p₂ = sqDist353 p₂ p₃ ∨
   sqDist353 p₁ p₃ = sqDist353 p₂ p₃)

/-- Three points form a right-angled triangle: all distinct with one angle equal
    to 90° (dot product of adjacent edges is zero at some vertex). -/
def IsRightTriangle353 (p₁ p₂ p₃ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
  ((p₂.1 - p₁.1) * (p₃.1 - p₁.1) + (p₂.2 - p₁.2) * (p₃.2 - p₁.2) = 0 ∨
   (p₁.1 - p₂.1) * (p₃.1 - p₂.1) + (p₁.2 - p₂.2) * (p₃.2 - p₂.2) = 0 ∨
   (p₁.1 - p₃.1) * (p₂.1 - p₃.1) + (p₁.2 - p₃.2) * (p₂.2 - p₃.2) = 0)

/-- Four points (in order) form an isosceles trapezoid: exactly one pair of
    parallel opposite sides, with the non-parallel sides (legs) of equal length.
    Here p₁p₂ ∥ p₄p₃ are the parallel sides and p₁p₄, p₂p₃ are the equal legs. -/
def IsIsoscelesTrapezoid353 (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  Parallel353 (p₂.1 - p₁.1, p₂.2 - p₁.2) (p₃.1 - p₄.1, p₃.2 - p₄.2) ∧
  sqDist353 p₁ p₄ = sqDist353 p₂ p₃ ∧
  ¬ Parallel353 (p₄.1 - p₁.1, p₄.2 - p₁.2) (p₃.1 - p₂.1, p₃.2 - p₂.2)

/-- Four distinct points lie on a common circle. -/
def IsCyclicQuadrilateral353 (p₁ p₂ p₃ p₄ : ℝ × ℝ) : Prop :=
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄ ∧
  ∃ (c : ℝ × ℝ) (r_sq : ℝ), 0 < r_sq ∧
    sqDist353 c p₁ = r_sq ∧ sqDist353 c p₂ = r_sq ∧
    sqDist353 c p₃ = r_sq ∧ sqDist353 c p₄ = r_sq

/--
Erdős Problem #353, Part 1 [Er83d]:

Let A ⊆ ℝ² be a measurable set with infinite Lebesgue measure. Must A contain
the vertices of an isosceles trapezoid of area 1?

Proved by Koizumi [Ko25].
-/
theorem erdos_problem_353_isosceles_trapezoid
    (A : Set (ℝ × ℝ))
    (hA_meas : MeasurableSet A)
    (hA_inf : volume A = ⊤) :
    ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
      IsIsoscelesTrapezoid353 p₁ p₂ p₃ p₄ ∧
      quadArea353 p₁ p₂ p₃ p₄ = 1 :=
  sorry

/--
Erdős Problem #353, Part 2 [Er83d]:

Must a measurable set A ⊆ ℝ² with infinite measure contain the vertices of an
isosceles triangle of area 1?

Proved by Koizumi [Ko25].
-/
theorem erdos_problem_353_isosceles_triangle
    (A : Set (ℝ × ℝ))
    (hA_meas : MeasurableSet A)
    (hA_inf : volume A = ⊤) :
    ∃ p₁ p₂ p₃ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧
      IsIsoscelesTriangle353 p₁ p₂ p₃ ∧
      triangleArea353 p₁ p₂ p₃ = 1 :=
  sorry

/--
Erdős Problem #353, Part 3 [Er83d]:

Must a measurable set A ⊆ ℝ² with infinite measure contain the vertices of a
right-angled triangle of area 1?

Proved by Koizumi [Ko25].
-/
theorem erdos_problem_353_right_triangle
    (A : Set (ℝ × ℝ))
    (hA_meas : MeasurableSet A)
    (hA_inf : volume A = ⊤) :
    ∃ p₁ p₂ p₃ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧
      IsRightTriangle353 p₁ p₂ p₃ ∧
      triangleArea353 p₁ p₂ p₃ = 1 :=
  sorry

/--
Erdős Problem #353, Part 4 [Er83d]:

Must a measurable set A ⊆ ℝ² with infinite measure contain four distinct points
on a common circle forming a quadrilateral of area 1?

Proved by Kovač and Predojević [KoPr24].
-/
theorem erdos_problem_353_cyclic_quadrilateral
    (A : Set (ℝ × ℝ))
    (hA_meas : MeasurableSet A)
    (hA_inf : volume A = ⊤) :
    ∃ p₁ p₂ p₃ p₄ : ℝ × ℝ,
      p₁ ∈ A ∧ p₂ ∈ A ∧ p₃ ∈ A ∧ p₄ ∈ A ∧
      IsCyclicQuadrilateral353 p₁ p₂ p₃ p₄ ∧
      quadArea353 p₁ p₂ p₃ p₄ = 1 :=
  sorry

end
