import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.BoundedVariation
import Mathlib.Algebra.Polynomial.Eval.Defs

open MeasureTheory Filter Set

/-!
# Erdős Problem #515

Let f(z) be an entire function, not a polynomial. Does there exist a locally
rectifiable path C tending to infinity such that, for every λ > 0, the integral
∫_C |f(z)|^{-λ} |dz| is finite?

This was proved in the affirmative. The case when f has finite order was proved
by Zhang [Zh77]. The general case was proved by Lewis, Rossi, and Weitsman
[LRW84], who in fact proved this with |f| replaced by e^u where u is any
subharmonic function.
-/

/--
Erdős Problem #515: For any entire function f that is not a polynomial, there
exists a locally rectifiable path γ tending to infinity such that for every
λ > 0, the line integral ∫_γ |f(z)|^{-λ} |dz| is finite.

The path γ : ℝ → ℂ is parametrized on [0, ∞), is continuous with locally bounded
variation (i.e., locally rectifiable), and satisfies ‖γ(t)‖ → ∞ as t → ∞.
The integral ∫_γ |f(z)|^{-λ} |dz| is expressed as ∫₀^∞ ‖f(γ(t))‖^{-λ} · ‖γ'(t)‖ dt.
-/
theorem erdos_problem_515 :
    ∀ (f : ℂ → ℂ),
      Differentiable ℂ f →
      (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      ∃ (γ : ℝ → ℂ),
        Continuous γ ∧
        LocallyBoundedVariationOn γ (Ici 0) ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop ∧
        ∀ l : ℝ, 0 < l →
          IntegrableOn
            (fun t => ‖f (γ t)‖ ^ (-l) * ‖deriv γ t‖)
            (Ici 0)
            volume :=
  sorry
