import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Polynomial Complex Real Finset BigOperators

noncomputable section

/-!
# Erdős Problem #990

Let f = a₀ + ⋯ + a_d xᵈ ∈ ℂ[x] be a polynomial. Is it true that, if f has
roots z₁, …, z_d with corresponding arguments θ₁, …, θ_d ∈ [0, 2π), then
for all intervals I ⊆ [0, 2π)

  |#{θ_i ∈ I} − |I|/(2π) · d| ≪ (n · log M)^{1/2}

where n is the number of non-zero coefficients of f and
M = (|a₀| + ⋯ + |a_d|) / (|a₀| · |a_d|)^{1/2}.

Erdős and Turán [ErTu50] proved such an upper bound with n replaced by d.
-/

/-- The argument of a complex number normalized to [0, 2π).
    Returns 0 for z = 0. -/
noncomputable def Complex.arg2pi (z : ℂ) : ℝ :=
  if Complex.arg z < 0 then Complex.arg z + 2 * Real.pi else Complex.arg z

/-- The number of roots (counted with multiplicity) of a polynomial whose
    argument lies in the interval [α, β]. -/
noncomputable def rootArgCount (f : Polynomial ℂ) (α β : ℝ) : ℕ :=
  (f.roots.map Complex.arg2pi).countP (fun θ => decide (α ≤ θ ∧ θ ≤ β))

/-- The Erdős–Turán measure M(f) = (|a₀| + ⋯ + |a_d|) / √(|a₀| · |a_d|). -/
noncomputable def erdosTuranMeasure (f : Polynomial ℂ) : ℝ :=
  (∑ i ∈ Finset.range (f.natDegree + 1), ‖f.coeff i‖) /
    Real.sqrt (‖f.coeff 0‖ * ‖f.leadingCoeff‖)

/--
Erdős Problem #990 [Er64b]:

Let f = a₀ + ⋯ + a_d xᵈ ∈ ℂ[x] be a polynomial with roots z₁, …, z_d
with corresponding arguments θ₁, …, θ_d ∈ [0, 2π). Is it true that for all
intervals [α, β] ⊆ [0, 2π),

  |#{θ_i ∈ [α, β]} − (β − α)/(2π) · d| ≤ C · √(n · log M)

where C is an absolute constant, n is the number of non-zero coefficients
of f, and M = (|a₀| + ⋯ + |a_d|) / √(|a₀| · |a_d|)?

Erdős and Turán proved such an upper bound with n replaced by d (the degree).
-/
theorem erdos_problem_990 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (f : Polynomial ℂ),
      f.natDegree ≥ 1 →
      f.coeff 0 ≠ 0 →
      ∀ (α β : ℝ), 0 ≤ α → α ≤ β → β ≤ 2 * Real.pi →
        |(rootArgCount f α β : ℝ) - (β - α) / (2 * Real.pi) * ↑f.natDegree| ≤
          C * Real.sqrt (↑f.support.card * Real.log (erdosTuranMeasure f)) :=
  sorry

end
