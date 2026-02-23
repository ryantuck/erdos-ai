import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Complex Filter Topology Set MeasureTheory

namespace Erdos1115

/-- An entire function: differentiable everywhere on ℂ. -/
def IsEntire (f : ℂ → ℂ) : Prop := Differentiable ℂ f

/-- An entire function has finite order: there exists ρ ≥ 0 such that
    |f(z)| ≤ exp(C · |z|^ρ) for all sufficiently large |z|. -/
def HasFiniteOrder (f : ℂ → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 ≤ ρ ∧ ∃ (C R : ℝ), 0 < R ∧
    ∀ z : ℂ, R ≤ ‖z‖ → ‖f z‖ ≤ Real.exp (C * ‖z‖ ^ ρ)

/-- An arc-length parameterized rectifiable path in ℂ going to infinity.
    The parameter t represents arc length from the start. -/
structure ArcLengthPath where
  toFun : ℝ → ℂ
  continuous' : Continuous toFun
  /-- The path goes to infinity: |γ(t)| → ∞ as t → ∞. -/
  tendsToInfinity : Tendsto (fun t => ‖toFun t‖) atTop atTop
  /-- Parameterized by arc length: the variation on [0, T] equals T. -/
  isArcLength : ∀ T : ℝ, 0 ≤ T → eVariationOn toFun (Icc 0 T) = ENNReal.ofReal T

/-- f(z) → ∞ along a path γ. -/
def TendsToInfinityAlong (f : ℂ → ℂ) (γ : ArcLengthPath) : Prop :=
  Tendsto (fun t => ‖f (γ.toFun t)‖) atTop atTop

/-- The arc length of an arc-length parameterized path γ inside the closed disk
    of radius r. For arc-length parameterization, this equals the Lebesgue measure
    of {t ≥ 0 : |γ(t)| ≤ r}. -/
noncomputable def pathLengthInDisk (γ : ArcLengthPath) (r : ℝ) : ℝ :=
  (volume (({t : ℝ | 0 ≤ t ∧ ‖γ.toFun t‖ ≤ r}) : Set ℝ)).toReal

/--
Erdős Problem #1115 (Disproved by Gol'dberg and Eremenko [GoEr79]):

Let f(z) be an entire function of finite order, and let Γ be a rectifiable path
on which f(z) → ∞. Let ℓ(r) be the length of Γ in the disc |z| < r.

Can such a path Γ always be found with ℓ(r) ≪ r?

Disproved: Gol'dberg and Eremenko showed that for any φ(r) → ∞ there is an
entire function f with log M(r) ≪ φ(r)(log r)² such that there is no path Γ
on which f(z) → ∞ and ℓ(r) ≪ r. They also construct such functions of any
prescribed finite order in [0, ∞).

Formally: there exists an entire function of finite order such that for every
arc-length parameterized path to infinity on which f → ∞, ℓ(r) is not O(r).
-/
theorem erdos_problem_1115 :
    ∃ f : ℂ → ℂ, IsEntire f ∧ HasFiniteOrder f ∧
      ∀ γ : ArcLengthPath, TendsToInfinityAlong f γ →
        ¬∃ (C R : ℝ), ∀ r : ℝ, R ≤ r → pathLengthInDisk γ r ≤ C * r :=
  sorry

end Erdos1115
