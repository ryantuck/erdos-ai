import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Multiset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section

/-!
# Erdős Problem #633

Classify those triangles which can only be cut into a square number of congruent
triangles.

Any triangle can be cut into n² congruent triangles for any n ≥ 1. Soifer [So09]
proved that there exists at least one triangle (e.g. one with sides √2, √3, √4)
which can only be cut into a square number of congruent triangles. In fact,
Soifer proved that any triangle for which the angles and sides are both
integrally independent has this property. The full classification remains open.
-/

/-- Squared Euclidean distance between two points in ℝ². -/
def sqDist633 (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Multiset of squared side lengths of a triangle.
    Two triangles are congruent (by SSS) iff these multisets agree. -/
def sideLengthsSq633 (A B C : ℝ × ℝ) : Multiset ℝ :=
  ↑[sqDist633 A B, sqDist633 B C, sqDist633 A C]

/-- A triangle is non-degenerate (vertices not collinear). -/
def NonDegenerate633 (A B C : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- The closed triangular region: convex hull of vertices A, B, C.
    A point p lies in the triangle iff p = αA + βB + γC for some
    α, β, γ ≥ 0 with α + β + γ = 1. -/
def triangleRegion633 (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- The open interior of a triangular region: strictly positive
    barycentric coordinates. -/
def triangleInterior633 (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- Triangle (A, B, C) can be dissected into exactly n pairwise-congruent
    non-degenerate triangles that tile it: each is contained in the original,
    their interiors are pairwise disjoint, and their union covers the original. -/
def CanDissectInto633 (A B C : ℝ × ℝ) (n : ℕ) : Prop :=
  ∃ (V : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)),
    -- All sub-triangles are non-degenerate
    (∀ i, NonDegenerate633 (V i).1 (V i).2.1 (V i).2.2) ∧
    -- All sub-triangles are mutually congruent (same squared side lengths)
    (∀ i j, sideLengthsSq633 (V i).1 (V i).2.1 (V i).2.2 =
            sideLengthsSq633 (V j).1 (V j).2.1 (V j).2.2) ∧
    -- Each sub-triangle is contained in the original
    (∀ i, triangleRegion633 (V i).1 (V i).2.1 (V i).2.2 ⊆
           triangleRegion633 A B C) ∧
    -- Pairwise disjoint interiors
    (∀ i j, i ≠ j →
      triangleInterior633 (V i).1 (V i).2.1 (V i).2.2 ∩
      triangleInterior633 (V j).1 (V j).2.1 (V j).2.2 = ∅) ∧
    -- Union covers the original triangle
    (∀ p, p ∈ triangleRegion633 A B C →
      ∃ i, p ∈ triangleRegion633 (V i).1 (V i).2.1 (V i).2.2)

/-- Euclidean distance (side length) between two points. -/
def sideLength633 (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist633 p q)

/-- The sides of a triangle are integrally independent: no nontrivial integer
    linear combination of the three side lengths equals zero. -/
def IntIndepSides633 (A B C : ℝ × ℝ) : Prop :=
  ∀ (a₁ a₂ a₃ : ℤ),
    ↑a₁ * sideLength633 B C + ↑a₂ * sideLength633 A C +
      ↑a₃ * sideLength633 A B = 0 →
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0

/-- The angle at vertex P in triangle PQR, via the dot-product formula:
    arccos((PQ⃗ · PR⃗) / (|PQ| · |PR|)). Returns a value in [0, π]. -/
def angle633 (P Q R : ℝ × ℝ) : ℝ :=
  Real.arccos (((Q.1 - P.1) * (R.1 - P.1) + (Q.2 - P.2) * (R.2 - P.2)) /
    (sideLength633 P Q * sideLength633 P R))

/-- The angles of a triangle are integrally independent: the only integer
    linear combination of the angles that equals an integer multiple of π
    is the trivial one (all coefficients equal). This accounts for the
    constraint α + β + γ = π. -/
def IntIndepAngles633 (A B C : ℝ × ℝ) : Prop :=
  ∀ (a₁ a₂ a₃ k : ℤ),
    ↑a₁ * angle633 A B C + ↑a₂ * angle633 B A C +
      ↑a₃ * angle633 C A B = ↑k * Real.pi →
    a₁ = a₂ ∧ a₂ = a₃

/--
Erdős Problem #633, Part 1 (known, folklore):

Every non-degenerate triangle can be dissected into n² congruent triangles
for any positive integer n.
-/
theorem erdos_problem_633_square_dissection
    (A B C : ℝ × ℝ) (hnd : NonDegenerate633 A B C)
    (n : ℕ) (hn : 1 ≤ n) :
    CanDissectInto633 A B C (n ^ 2) :=
  sorry

/--
Erdős Problem #633, Part 2 (Soifer [So09]):

There exists a non-degenerate triangle which can be dissected into n
congruent triangles only when n is a perfect square.
-/
theorem erdos_problem_633_only_squares_exist :
    ∃ A B C : ℝ × ℝ, NonDegenerate633 A B C ∧
    ∀ n : ℕ, 1 ≤ n → CanDissectInto633 A B C n → ∃ m : ℕ, n = m ^ 2 :=
  sorry

/--
Erdős Problem #633, Part 3 (Soifer [So09]):

If a non-degenerate triangle has integrally independent sides and angles,
then it can only be dissected into a perfect square number of congruent
triangles.
-/
theorem erdos_problem_633_soifer_sufficient
    (A B C : ℝ × ℝ) (hnd : NonDegenerate633 A B C)
    (hsides : IntIndepSides633 A B C) (hangles : IntIndepAngles633 A B C) :
    ∀ n : ℕ, 1 ≤ n → CanDissectInto633 A B C n → ∃ m : ℕ, n = m ^ 2 :=
  sorry

end
