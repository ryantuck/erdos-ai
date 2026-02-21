import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

/--
Erdős Problem #226 [Er57] — SOLVED

Is there an entire non-linear function f such that, for all x ∈ ℝ, x is rational if and
only if f(x) is?

Solved by Barth and Schneider [BaSc70], who proved that if A, B ⊂ ℝ are countable dense
sets then there exists a transcendental entire function f such that f(z) ∈ B if and only
if z ∈ A. In [BaSc71] they proved the same result for countable dense subsets of ℂ.
-/
theorem erdos_problem_226 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (¬∃ a b : ℂ, ∀ z, f z = a * z + b) ∧
      (∀ x : ℝ, (∃ q : ℚ, (q : ℝ) = x) ↔ ∃ q : ℚ, (q : ℂ) = f ↑x) :=
  sorry
