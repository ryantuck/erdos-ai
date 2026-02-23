import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Basic

open Nat Finset Filter Set Classical

/-- Count of natural numbers n in {1, ..., N} with φ(n) < c · n -/
noncomputable def totientDensityCount (c : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun n => 0 < n ∧ (Nat.totient n : ℝ) < c * ↑n)).card

/--
Erdős Problem #50:
Schoenberg proved that for every c ∈ [0,1] the natural density of
{n ∈ ℕ : φ(n) < cn} exists. Let this density be denoted by f(c).
Is it true that there are no x such that f'(x) exists and is positive?

Erdős proved the distribution function f is purely singular.
-/
theorem erdos_problem_50_conjecture :
    ∀ f : ℝ → ℝ,
      (∀ c ∈ Icc (0 : ℝ) 1,
        Tendsto (fun N : ℕ => (totientDensityCount c N : ℝ) / ↑N) atTop (nhds (f c))) →
      ∀ x d : ℝ, HasDerivAt f d x → d ≤ 0 :=
  sorry
