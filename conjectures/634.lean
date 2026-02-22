import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic

noncomputable section

/-!
# Erdős Problem #634

Find all n such that there is at least one triangle which can be cut into n
congruent triangles.

It is easy to see that all square numbers have this property (any triangle can
be cut into n² congruent copies). Soifer [So09c] showed that numbers of the
form 2n², 3n², 6n², and n² + m² also have this property. Beeson showed that
7 and 11 do not have this property. It is possible that any prime of the form
4n + 3 does not have this property. In particular, it is not known whether 19
has this property.
-/

/-- Squared Euclidean distance between two points in ℝ². -/
def sqDist634 (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Multiset of squared side lengths of a triangle.
    Two triangles are congruent (by SSS) iff these multisets agree. -/
def sideLengthsSq634 (A B C : ℝ × ℝ) : Multiset ℝ :=
  ↑[sqDist634 A B, sqDist634 B C, sqDist634 A C]

/-- A triangle is non-degenerate (vertices not collinear). -/
def NonDegenerate634 (A B C : ℝ × ℝ) : Prop :=
  (B.1 - A.1) * (C.2 - A.2) - (C.1 - A.1) * (B.2 - A.2) ≠ 0

/-- The closed triangular region: convex hull of vertices A, B, C.
    A point p lies in the triangle iff p = αA + βB + γC for some
    α, β, γ ≥ 0 with α + β + γ = 1. -/
def triangleRegion634 (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- The open interior of a triangular region: strictly positive
    barycentric coordinates. -/
def triangleInterior634 (A B C : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ (α β γ : ℝ), 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧
    p.1 = α * A.1 + β * B.1 + γ * C.1 ∧
    p.2 = α * A.2 + β * B.2 + γ * C.2}

/-- Triangle (A, B, C) can be dissected into exactly n pairwise-congruent
    non-degenerate triangles that tile it: each is contained in the original,
    their interiors are pairwise disjoint, and their union covers the original. -/
def CanDissectInto634 (A B C : ℝ × ℝ) (n : ℕ) : Prop :=
  ∃ (V : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ)),
    -- All sub-triangles are non-degenerate
    (∀ i, NonDegenerate634 (V i).1 (V i).2.1 (V i).2.2) ∧
    -- All sub-triangles are mutually congruent (same squared side lengths)
    (∀ i j, sideLengthsSq634 (V i).1 (V i).2.1 (V i).2.2 =
            sideLengthsSq634 (V j).1 (V j).2.1 (V j).2.2) ∧
    -- Each sub-triangle is contained in the original
    (∀ i, triangleRegion634 (V i).1 (V i).2.1 (V i).2.2 ⊆
           triangleRegion634 A B C) ∧
    -- Pairwise disjoint interiors
    (∀ i j, i ≠ j →
      triangleInterior634 (V i).1 (V i).2.1 (V i).2.2 ∩
      triangleInterior634 (V j).1 (V j).2.1 (V j).2.2 = ∅) ∧
    -- Union covers the original triangle
    (∀ p, p ∈ triangleRegion634 A B C →
      ∃ i, p ∈ triangleRegion634 (V i).1 (V i).2.1 (V i).2.2)

/-- There exists a triangle that can be dissected into n congruent triangles. -/
def HasCongruentDissection (n : ℕ) : Prop :=
  ∃ A B C : ℝ × ℝ, NonDegenerate634 A B C ∧ CanDissectInto634 A B C n

/--
Erdős Problem #634, Part 1 (known, folklore):

Every square number n² (with n ≥ 1) has the property: any triangle can be
cut into n² congruent triangles.
-/
theorem erdos_634_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (n ^ 2) :=
  sorry

/--
Erdős Problem #634, Part 2 (Soifer [So09c]):

For any positive integer n, the number 2n² has a congruent dissection.
-/
theorem erdos_634_two_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (2 * n ^ 2) :=
  sorry

/--
Erdős Problem #634, Part 3 (Soifer [So09c]):

For any positive integer n, the number 3n² has a congruent dissection.
-/
theorem erdos_634_three_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (3 * n ^ 2) :=
  sorry

/--
Erdős Problem #634, Part 4 (Soifer [So09c]):

For any positive integer n, the number 6n² has a congruent dissection.
-/
theorem erdos_634_six_squares (n : ℕ) (hn : 1 ≤ n) :
    HasCongruentDissection (6 * n ^ 2) :=
  sorry

/--
Erdős Problem #634, Part 5 (Soifer [So09c]):

For any positive integers n and m, the number n² + m² has a congruent
dissection.
-/
theorem erdos_634_sum_of_squares (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    HasCongruentDissection (n ^ 2 + m ^ 2) :=
  sorry

/--
Erdős Problem #634, Part 6 (Beeson):

There is no triangle that can be cut into exactly 7 congruent triangles.
-/
theorem erdos_634_not_seven : ¬ HasCongruentDissection 7 :=
  sorry

/--
Erdős Problem #634, Part 7 (Beeson):

There is no triangle that can be cut into exactly 11 congruent triangles.
-/
theorem erdos_634_not_eleven : ¬ HasCongruentDissection 11 :=
  sorry

/--
Erdős Problem #634 (open conjecture):

Characterize the set of all n for which HasCongruentDissection n holds.
A complete characterization is sought. It is conjectured that no prime of the
form 4k + 3 has this property.
-/
theorem erdos_634_conjecture :
    ∀ p : ℕ, Nat.Prime p → p % 4 = 3 → ¬ HasCongruentDissection p :=
  sorry

end
