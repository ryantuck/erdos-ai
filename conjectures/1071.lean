import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable

open Set

noncomputable section

/-!
# Erdős Problem #1071

Is there a finite set of unit line segments (rotated and translated copies of
(0,1)) in the unit square, no two of which intersect, which are maximal with
respect to this property?

Is there a region R with a maximal set of disjoint unit line segments that is
countably infinite?

A question of Erdős and Tóth [Er87b, p.173].
The answer to the first question is yes (proved by Danzer).
Alexeev proved that the unit square itself admits a countably infinite maximal
such set.
-/

/-- A segment in ℝ² given by its two endpoints. -/
structure Seg where
  p : ℝ × ℝ
  q : ℝ × ℝ

/-- The open point set of a segment (excluding endpoints), representing a
    rotated and translated copy of the open interval (0,1). -/
def Seg.pointSet (s : Seg) : Set (ℝ × ℝ) :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = (1 - t) • s.p + t • s.q}

/-- A segment has unit length (squared Euclidean distance between endpoints
    equals 1). -/
def Seg.isUnit (s : Seg) : Prop :=
  (s.p.1 - s.q.1) ^ 2 + (s.p.2 - s.q.2) ^ 2 = 1

/-- The unit square [0,1]² ⊂ ℝ². -/
def unitSquare : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ x.1 ≤ 1 ∧ 0 ≤ x.2 ∧ x.2 ≤ 1}

/-- A set of segments S in region R is a maximal packing of disjoint open unit
    segments if:
    (1) every segment is unit-length with its open interior contained in R,
    (2) the open interiors are pairwise disjoint, and
    (3) every unit segment whose open interior lies in R has nonempty
        intersection with some member of S. -/
def IsMaximalDisjointUnitSegs (S : Set Seg) (R : Set (ℝ × ℝ)) : Prop :=
  (∀ s ∈ S, s.isUnit ∧ s.pointSet ⊆ R) ∧
  (∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → Disjoint s₁.pointSet s₂.pointSet) ∧
  ∀ s : Seg, s.isUnit → s.pointSet ⊆ R →
    ∃ s' ∈ S, ¬Disjoint s.pointSet s'.pointSet

/--
Erdős Problem #1071, Part (a) [Er87b, p.173]:

There exists a finite maximal set of pairwise disjoint open unit segments
in the unit square. (Proved by Danzer.)
-/
theorem erdos_problem_1071a :
    ∃ S : Set Seg, S.Finite ∧ IsMaximalDisjointUnitSegs S unitSquare :=
  sorry

/--
Erdős Problem #1071, Part (b) [Er87b, p.173]:

There exists a region R ⊆ ℝ² with a countably infinite maximal set of
pairwise disjoint unit segments. (Proved by Alexeev for the unit square.)
-/
theorem erdos_problem_1071b :
    ∃ R : Set (ℝ × ℝ), ∃ S : Set Seg,
      S.Countable ∧ Set.Infinite S ∧ IsMaximalDisjointUnitSegs S R :=
  sorry

end
