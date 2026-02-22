import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Real.Basic

/--
Erdős Problem #907 (proved by de Bruijn [dB51]):

Let f : ℝ → ℝ be such that for every h > 0, the function x ↦ f(x + h) - f(x)
is continuous. Is it true that f = g + φ for some continuous g and additive φ
(i.e., φ(x + y) = φ(x) + φ(y))?

Answered in the affirmative by de Bruijn.
-/
theorem erdos_problem_907 (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, h > 0 → Continuous (fun x => f (x + h) - f x)) :
    ∃ g φ : ℝ → ℝ, Continuous g ∧ (∀ x y : ℝ, φ (x + y) = φ x + φ y) ∧
      ∀ x : ℝ, f x = g x + φ x :=
  sorry
