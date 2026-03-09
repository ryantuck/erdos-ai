import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Countable

open Set

noncomputable section

/-- An open unit segment in ℝ²: the set {p + t • d | 0 < t < 1}. -/
def OpenUnitSegment (p d : EuclideanSpace ℝ (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∃ t : ℝ, 0 < t ∧ t < 1 ∧ x = p + t • d}

/-- The closed unit square [0,1]² in ℝ². -/
def UnitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/--
A family of unit segments in a region R is a maximal pairwise-disjoint family if:
(1) all directions are unit vectors,
(2) every segment lies in R,
(3) distinct segments are disjoint, and
(4) every unit segment contained in R meets some member of the family.
-/
def IsMaximalDisjointFamily
    (R : Set (EuclideanSpace ℝ (Fin 2)))
    (S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))) : Prop :=
  (∀ pd ∈ S, ‖pd.2‖ = 1) ∧
  (∀ pd ∈ S, OpenUnitSegment pd.1 pd.2 ⊆ R) ∧
  (∀ pd₁ ∈ S, ∀ pd₂ ∈ S, pd₁ ≠ pd₂ →
    Disjoint (OpenUnitSegment pd₁.1 pd₁.2) (OpenUnitSegment pd₂.1 pd₂.2)) ∧
  (∀ p d : EuclideanSpace ℝ (Fin 2), ‖d‖ = 1 → OpenUnitSegment p d ⊆ R →
    ∃ pd ∈ S, (OpenUnitSegment p d ∩ OpenUnitSegment pd.1 pd.2).Nonempty)

/--
Erdős Problem #1071, first part [Er87b, p.173]:

Is there a finite set of unit line segments (rotated and translated copies of
the open interval (0,1)) in the unit square, no two of which intersect,
which are maximal with respect to this property?

A question of Erdős and Tóth. The answer is yes, proved by Danzer.
-/
theorem erdos_problem_1071a :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      S.Finite ∧ IsMaximalDisjointFamily UnitSquare S :=
  sorry

/--
Erdős Problem #1071, second part [Er87b, p.173]:

Is there a region R with a maximal set of disjoint unit line segments that is
countably infinite?

Alexeev proved that the unit square itself admits a countably infinite maximal
family.
-/
theorem erdos_problem_1071b :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      S.Countable ∧ S.Infinite ∧ IsMaximalDisjointFamily UnitSquare S :=
  sorry

end
