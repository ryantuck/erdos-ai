import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

open Polynomial Classical

noncomputable section

/-!
# Erdős Problem #1039

Let f(z) = ∏ᵢ₌₁ⁿ (z - zᵢ) ∈ ℂ[z] with |zᵢ| ≤ 1 for all i. Let ρ(f) be
the radius of the largest disc contained in {z : |f(z)| < 1}.

Is it true that ρ(f) ≫ 1/n?

A problem of Erdős, Herzog, and Piranian [EHP58, p.134].

Known results:
- f(z) = zⁿ - 1 gives ρ(f) ≤ π/(2n)
- Pommerenke [Po61] proved ρ(f) ≥ 1/(2en²)
- Krishnapur, Lundberg, Ramachandran [KLR25] proved ρ(f) ≫ 1/(n√(log n))
-/

/-- The sublevel radius ρ(f): the supremum of radii r > 0 such that some open
    disc of radius r is contained in {z : ‖f(z)‖ < 1}. -/
noncomputable def sublevelRadius (f : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | r > 0 ∧ ∃ c : ℂ, Metric.ball c r ⊆ {z : ℂ | ‖f.eval z‖ < 1}}

/--
Erdős Problem #1039 [EHP58, p.134]:

For monic complex polynomials of degree n ≥ 1 with all roots in the closed
unit disk, the sublevel radius ρ(f) is at least C/n for some absolute
constant C > 0.
-/
theorem erdos_problem_1039 :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : Polynomial ℂ),
      1 ≤ n → f.Monic → f.natDegree = n →
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) →
      sublevelRadius f ≥ C / (n : ℝ) :=
  sorry

end
