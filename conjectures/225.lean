import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators MeasureTheory

noncomputable section

/-!
# Erdős Problem #225

Let f(θ) = ∑_{k=0}^{n} c_k e^{ikθ} be a trigonometric polynomial all of whose
roots are real (equivalently, the polynomial P(z) = ∑ c_k z^k has all roots on
the unit circle), with max_{θ ∈ [0,2π]} |f(θ)| = 1. Then ∫₀²π |f(θ)| dθ ≤ 4.

This was proved independently by Kristiansen [Kr74] (for real c_k) and
Saff and Sheil-Small [SaSh74] (for complex c_k).
-/

/-- A trigonometric polynomial: f(θ) = ∑_{k=0}^{n} c_k e^{ikθ} -/
def trigPoly (n : ℕ) (c : ℕ → ℂ) (θ : ℝ) : ℂ :=
  ∑ k ∈ range (n + 1), c k * Complex.exp (↑k * ↑θ * Complex.I)

/--
Erdős Problem #225 [Er40b, Er57, Er61, Ha74]:

If f(θ) = ∑_{k=0}^{n} c_k e^{ikθ} is a trigonometric polynomial whose
associated algebraic polynomial P(z) = ∑ c_k z^k has all roots on the
unit circle, and max_θ |f(θ)| = 1, then ∫₀²π |f(θ)| dθ ≤ 4.
-/
theorem erdos_problem_225 (n : ℕ) (c : ℕ → ℂ)
    (hn : 0 < n)
    (hlead : c n ≠ 0)
    -- All roots of P(z) = ∑ c_k z^k lie on the unit circle
    (hroots : ∀ z : ℂ, (∑ k ∈ range (n + 1), c k * z ^ k) = 0 → ‖z‖ = 1)
    -- max_θ |f(θ)| = 1
    (hbound : ∀ θ : ℝ, ‖trigPoly n c θ‖ ≤ 1)
    (hattained : ∃ θ : ℝ, ‖trigPoly n c θ‖ = 1) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖trigPoly n c θ‖ ≤ 4 :=
  sorry

end
