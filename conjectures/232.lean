import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory Metric

noncomputable section

/-!
# Erdős Problem #232

For A ⊂ ℝ² we define the upper density as
  δ̄(A) = limsup_{R→∞} λ(A ∩ B_R) / λ(B_R),
where λ is the Lebesgue measure and B_R is the ball of radius R.

Estimate m₁ = sup δ̄(A), where A ranges over all measurable subsets of ℝ²
without two points distance 1 apart. In particular, is m₁ ≤ 1/4?

Originally a question of Moser [Mo66]. The trivial upper bound is m₁ ≤ 1/2,
since for any unit vector u the sets A and A + u must be disjoint.
A lower bound of m₁ ≥ π/(8√3) ≈ 0.2267 comes from the union of open
circular discs of radius 1/2 at a regular hexagonal lattice.

PROVED by Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki [ACMVZ23],
who showed m₁ ≤ 0.247 < 1/4.
-/

/-- A set in a metric space is unit-distance-free if no two points in the set
    are exactly distance 1 apart. -/
def IsUnitDistanceFree {X : Type*} [PseudoMetricSpace X] (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist x y ≠ 1

/--
Erdős Problem #232 [Er85, p.4] (PROVED):

For every measurable unit-distance-free set A ⊆ ℝ², the upper density
  limsup_{R→∞} λ(A ∩ B_R) / λ(B_R) ≤ 1/4.

Formalized as: for every ε > 0, for all sufficiently large R, the density
ratio λ(A ∩ B_R) / λ(B_R) ≤ 1/4 + ε. This is equivalent to the limsup
being at most 1/4.

Proved by Ambrus–Csiszárik–Matolcsi–Varga–Zsámboki [ACMVZ23] who showed
the stronger bound m₁ ≤ 0.247.
-/
theorem erdos_problem_232 (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : MeasurableSet A)
    (hfree : IsUnitDistanceFree A)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      (volume (A ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)).toReal /
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)).toReal ≤ 1 / 4 + ε := by
  sorry

end
