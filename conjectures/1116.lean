import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

noncomputable section
open Complex Set

namespace Erdos1116

/-- The counting function n(r, a, f): the number of solutions to f(z) = a
    in the open disk {z : ℂ | ‖z‖ < r}. Uses Set.ncard (natural cardinality). -/
def rootCount (f : ℂ → ℂ) (r : ℝ) (a : ℂ) : ℕ :=
  Set.ncard {z : ℂ | f z = a ∧ ‖z‖ < r}

/--
Erdős Problem #1116 (Solved by Gol'dberg [Go78] and Toppila [To76]):

For a meromorphic function f, let n(r,a) count the number of roots of f(z) = a
in the disc |z| < r. Does there exist a meromorphic (or entire) f such that
for every a ≠ b, limsup_{r→∞} n(r,a)/n(r,b) = ∞?

Gol'dberg and Toppila independently constructed entire functions with this property.

The limsup = ∞ condition is expressed multiplicatively: for every M and R,
there exists r > R with n(r,a) > M · n(r,b).
-/
theorem erdos_problem_1116 :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      ∀ a b : ℂ, a ≠ b →
        ∀ (M : ℝ) (R : ℝ), ∃ r : ℝ, r > R ∧
          M * (rootCount f r b : ℝ) < (rootCount f r a : ℝ) :=
  sorry

end Erdos1116
