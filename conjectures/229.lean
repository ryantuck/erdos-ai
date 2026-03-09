import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Set.Finite.Basic

open Complex Metric

/--
A set S ⊆ ℂ has no finite limit point: every closed ball in ℂ contains only
finitely many points of S.
-/
def NoFiniteLimitPoint (S : Set ℂ) : Prop :=
  ∀ R : ℝ, (S ∩ closedBall 0 R).Finite

/--
A function f : ℂ → ℂ is entire and transcendental: it is differentiable
everywhere and is not equal to any polynomial.
-/
def EntireTranscendental (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ¬∃ p : Polynomial ℂ, ∀ z, f z = p.eval z

/--
Erdős Problem #229 [Er57, Er61, Ha74, Er82e]:

Let (Sₙ) be a sequence of sets of complex numbers, none of which have a finite
limit point. Does there exist an entire transcendental function f(z) such that,
for all n ≥ 1, there exists some kₙ ≥ 0 such that f⁽ᵏⁿ⁾(z) = 0 for all z ∈ Sₙ?

Solved in the affirmative by Barth and Schneider [BaSc72].
-/
theorem erdos_problem_229
    (S : ℕ → Set ℂ)
    (hS : ∀ n, NoFiniteLimitPoint (S n)) :
    ∃ f : ℂ → ℂ, EntireTranscendental f ∧
      ∀ n, ∃ k : ℕ, ∀ z ∈ S n, iteratedDeriv k f z = 0 :=
  sorry
