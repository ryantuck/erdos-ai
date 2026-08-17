import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

noncomputable section
open Complex Set

namespace Erdos1117

/-- A function f : ℂ → ℂ is a monomial if f(z) = c * z^n for some constant c
    and natural number n. -/
def IsMonomial (f : ℂ → ℂ) : Prop :=
  ∃ (c : ℂ) (n : ℕ), ∀ z, f z = c * z ^ n

/-- The maximum modulus of f on the circle of radius r:
    M(r) = sup{‖f(z)‖ : ‖z‖ = r}. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/-- ν(r) counts the number of z with ‖z‖ = r achieving the maximum modulus
    of f. This is finite when f is entire and not a monomial. -/
noncomputable def nu (f : ℂ → ℂ) (r : ℝ) : ℕ :=
  Set.ncard {z : ℂ | ‖z‖ = r ∧ ‖f z‖ = maxModulus f r}

/--
Erdős Problem #1117 [Ha74] — OPEN

This is Problem 2.16 from [Ha74].

Let f(z) be an entire function which is not a monomial. Let ν(r) count the
number of z with |z| = r such that |f(z)| = max_{|z|=r} |f(z)|.
(This is a finite quantity if f is not a monomial.)

Is it possible for liminf_{r→∞} ν(r) = ∞?

The analogous question for limsup was answered affirmatively by Herzog and
Piranian [HePi68]. The liminf question remains open. An 'approximate'
affirmative answer is given by Glücksam and Pardo-Simón [GlPa24].

The conjecture formalized here captures the existence of such a function:
for every N, eventually ν(r) ≥ N for all sufficiently large r.
-/
theorem erdos_problem_1117 :
    answer(sorry) ↔ ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬IsMonomial f ∧
      ∀ N : ℕ, ∃ R : ℝ, ∀ r : ℝ, R ≤ r → N ≤ nu f r :=
  sorry

/-- Variant (solved affirmatively): the analogous question for limsup instead of liminf.
    Answered by Herzog and Piranian [HePi68]. -/
theorem erdos_problem_1117_limsup :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ ¬IsMonomial f ∧
      ∀ N : ℕ, ∃ r : ℝ, N ≤ nu f r := by
  sorry

end Erdos1117
