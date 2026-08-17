import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

/--
Erdős Problem #1126 (proved independently by de Bruijn [dB66] and Jurkat [Ju65]):

If f(x+y) = f(x) + f(y) for almost all x, y ∈ ℝ then there exists a function g
such that g(x+y) = g(x) + g(y) for all x, y ∈ ℝ and f(x) = g(x) for almost all x.
-/
theorem erdos_problem_1126 (f : ℝ → ℝ)
    (hf : ∀ᵐ p : ℝ × ℝ ∂(volume.prod volume), f (p.1 + p.2) = f p.1 + f p.2) :
    ∃ g : ℝ → ℝ,
      (∀ x y : ℝ, g (x + y) = g x + g y) ∧
      (∀ᵐ x ∂volume, f x = g x) :=
  sorry
