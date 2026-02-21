import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex Filter Topology

noncomputable section

/-!
# Erdős Problem #514 (PARTIALLY PROVED)

Let $f(z)$ be an entire transcendental function. Does there exist a path $L$ so that,
for every $n$, $|f(z)/z^n| \to \infty$ as $z \to \infty$ along $L$?

Can the length of this path be estimated in terms of $M(r) = \max_{|z|=r} |f(z)|$?
Does there exist a path along which $|f(z)|$ tends to $\infty$ faster than a fixed
function of $M(r)$ (such as $M(r)^\varepsilon$)?

Boas (unpublished) proved the first part, that such a path must exist.
-/

/-- The maximum modulus of `f` on the circle of radius `r`:
    M(r) = sup { ‖f(z)‖ | ‖z‖ = r }. -/
def maxModulus514 (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- Erdős Problem #514, Part 1 (PROVED by Boas, unpublished):
    For every entire transcendental function f, there exists a continuous path γ
    going to infinity such that |f(γ(t))/γ(t)^n| → ∞ for every n. -/
theorem erdos_problem_514_part1 :
    ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      ∃ γ : ℝ → ℂ, Continuous γ ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop ∧
        ∀ n : ℕ, Tendsto (fun t => ‖f (γ t)‖ / ‖γ t‖ ^ n) atTop atTop :=
  sorry

/-- Erdős Problem #514, Part 2 (OPEN):
    For every entire transcendental function f and every ε > 0, does there exist a
    continuous path γ going to infinity along which |f(z)| ≥ M(|z|)^ε? -/
theorem erdos_problem_514_part2 :
    ∀ f : ℂ → ℂ, Differentiable ℂ f →
      (¬ ∃ p : Polynomial ℂ, ∀ z, f z = p.eval z) →
      ∀ ε : ℝ, 0 < ε →
        ∃ γ : ℝ → ℂ, Continuous γ ∧
          Tendsto (fun t => ‖γ t‖) atTop atTop ∧
          ∀ᶠ t in atTop, (maxModulus514 f ‖γ t‖) ^ ε ≤ ‖f (γ t)‖ :=
  sorry

end
