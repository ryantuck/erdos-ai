import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Defs.Basic

open scoped Topology

/--
An entire function f : ℂ → ℂ is transcendental if it is not equal to the
evaluation of any polynomial.
-/
def IsTranscendentalEntire (f : ℂ → ℂ) : Prop :=
  ∀ p : Polynomial ℂ, f ≠ fun z => p.eval z

/--
Erdős Problem #906 [Er56d, Er82e]:

Is there an entire non-zero transcendental function f : ℂ → ℂ such that, for any
strictly increasing sequence n₁ < n₂ < ⋯, the set
  { z : f⁽ⁿₖ⁾(z) = 0 for some k ≥ 1 }
is everywhere dense in ℂ?

The problem is trivial for polynomials (Tang), so the function is assumed to be
transcendental. Erdős [Er82e] writes that this was solved affirmatively 'more
than ten years ago' but gives no reference.
-/
theorem erdos_problem_906 :
    ∃ f : ℂ → ℂ,
      IsTranscendentalEntire f ∧
      Differentiable ℂ f ∧
      ∀ n : ℕ → ℕ, StrictMono n →
        Dense {z : ℂ | ∃ k, iteratedDeriv (n k) f z = 0} :=
  sorry
