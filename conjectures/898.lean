import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

/-!
# Erdős Problem #898 (Erdős-Mordell Inequality)

If A, B, C ∈ ℝ² form a triangle and P is a point in the interior then,
if N is where the perpendicular from P to AB meets the triangle, and
similarly for M and L,
  PA + PB + PC ≥ 2(PM + PN + PL).

Conjectured by Erdős in 1932 and proved by Mordell soon afterwards,
now known as the Erdős-Mordell inequality.
-/

/-- Squared Euclidean distance between two points in ℝ². -/
def sqDist898 (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Euclidean distance between two points in ℝ². -/
def dist898 (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist898 p q)

/-- A triangle is non-degenerate (vertices not collinear). -/
def NonDegenerate898 (A B C : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- Point P lies in the open interior of triangle ABC
    (strictly positive barycentric coordinates). -/
def InInterior898 (P A B C : ℝ × ℝ) : Prop :=
  ∃ (α β γ : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    P.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    P.2 = α * A.2 + β * B.2 + γ * C.2

/-- The foot of the perpendicular from point P to the line through A and B.
    This is the orthogonal projection of P onto line AB:
    foot = A + t * (B - A) where t = ((P - A) · (B - A)) / |B - A|². -/
def perpFoot898 (P A B : ℝ × ℝ) : ℝ × ℝ :=
  let dx := B.1 - A.1
  let dy := B.2 - A.2
  let t := ((P.1 - A.1) * dx + (P.2 - A.2) * dy) / (dx ^ 2 + dy ^ 2)
  (A.1 + t * dx, A.2 + t * dy)

/--
Erdős Problem #898 (Erdős-Mordell Inequality) [Er82e, p.61]:

If A, B, C form a non-degenerate triangle in ℝ² and P is a point in its
interior, then
  dist(P, A) + dist(P, B) + dist(P, C)
    ≥ 2 * (dist(P, D_a) + dist(P, D_b) + dist(P, D_c))
where D_a, D_b, D_c are the feet of the perpendiculars from P to sides
BC, CA, AB respectively.

Conjectured by Erdős in 1932 and proved by Mordell soon afterwards.
-/
theorem erdos_problem_898
    (A B C P : ℝ × ℝ)
    (hnd : NonDegenerate898 A B C)
    (hP : InInterior898 P A B C) :
    dist898 P A + dist898 P B + dist898 P C ≥
      2 * (dist898 P (perpFoot898 P B C) +
           dist898 P (perpFoot898 P A C) +
           dist898 P (perpFoot898 P A B)) :=
  sorry

end
