import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

/-- The unit square [0,1]² in ℝ². -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ i, 0 ≤ p i ∧ p i ≤ 1}

/--
Erdős Problem #1124 (Tarski's circle-squaring problem, proved):

Can a square and a circle of the same area be decomposed into a finite number
of congruent parts?

A problem of Tarski, which Erdős described as 'a very beautiful problem...if it
were my problem I would offer $1000 for it'.

Laczkovich [La90b] proved that this is possible using translations only.

Formally: the unit square and the closed disk of radius 1/√π (both having area 1)
can be partitioned into finitely many pieces such that corresponding pieces are
congruent (related by isometries of ℝ²).
-/
theorem erdos_problem_1124 :
    ∃ (n : ℕ),
    ∃ (pieces_sq pieces_disk : Fin n → Set (EuclideanSpace ℝ (Fin 2))),
      -- The pieces partition the unit square
      (⋃ i, pieces_sq i) = unitSquare ∧
      (∀ i j, i ≠ j → Disjoint (pieces_sq i) (pieces_sq j)) ∧
      -- The pieces partition the closed disk of radius 1/√π (same area as unit square)
      (⋃ i, pieces_disk i) = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 / Real.sqrt Real.pi) ∧
      (∀ i j, i ≠ j → Disjoint (pieces_disk i) (pieces_disk j)) ∧
      -- Corresponding pieces are congruent (related by an isometry)
      (∀ i, ∃ f : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
        Isometry f ∧ f '' (pieces_sq i) = pieces_disk i) :=
  sorry

end
