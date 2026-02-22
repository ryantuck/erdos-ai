import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped ENNReal
open MeasureTheory Classical Filter Finset

noncomputable section

/-!
# Erdős Problem #1040

Let F ⊆ ℂ be a closed infinite set, and let μ(F) be the infimum of
|{z : |f(z)| < 1}| (Lebesgue measure), as f ranges over all polynomials of
the shape ∏(z - zᵢ) with zᵢ ∈ F.

Is μ(F) = 0 whenever the transfinite diameter of F is ≥ 1?

A problem of Erdős, Herzog, and Piranian [EHP58, p.135].

The transfinite diameter (logarithmic capacity) of F is defined by
  ρ(F) = lim_{n → ∞} sup_{z₁,...,zₙ ∈ F} (∏_{i<j} |zᵢ - zⱼ|)^(1/C(n,2)).

Erdős, Herzog, and Piranian showed the answer is yes when F is a line segment
or disc. Aletheia [Fe26] showed that μ(F) is not determined by the transfinite
diameter of F in general.
-/

/-- The product of pairwise distances ∏_{i<j} ‖z i - z j‖ for a tuple of
    complex numbers. -/
noncomputable def pairwiseDistProd {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The n-th transfinite diameter of F ⊆ ℂ:
    d_n(F) = sup_{z₁,...,zₙ ∈ F} (∏_{i<j} |zᵢ - zⱼ|)^(2/(n(n-1))). -/
noncomputable def nthTransfiniteDiam (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of F ⊆ ℂ:
    ρ(F) = lim_{n → ∞} d_n(F). -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam F n))

/-- The sublevel set measure μ(F, μ): infimum of μ({z : ‖f(z)‖ < 1}) over
    all monic polynomials with roots in F. Uses Fin (n+1) to ensure at least
    one root. -/
noncomputable def sublevelMeasure (F : Set ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (z : Fin (n + 1) → ℂ) (_ : ∀ i, z i ∈ F),
    μ {w : ℂ | ‖(univ : Finset (Fin (n + 1))).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem #1040 [EHP58, p.135]:

Let F ⊆ ℂ be a closed infinite set with transfinite diameter ≥ 1. Then
μ(F) = 0, i.e. the infimum of the Lebesgue measure of {z : |f(z)| < 1}
over monic polynomials with all roots in F is zero. The result holds for
any add Haar measure on ℂ.
-/
theorem erdos_problem_1040 (F : Set ℂ) (hF : IsClosed F) (hFinf : F.Infinite)
    (hd : transfiniteDiameter F ≥ 1)
    {μ : Measure ℂ} [μ.IsAddHaarMeasure] :
    sublevelMeasure F μ = 0 :=
  sorry

end
