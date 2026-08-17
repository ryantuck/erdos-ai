import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Real.Basic

/--
Erdős Problem #1125 (Proved by Laczkovich [La84]):
Let f : ℝ → ℝ be such that 2f(x) ≤ f(x+h) + f(x+2h) for every x ∈ ℝ and h > 0.
Must f be monotonic?

A problem of Kemperman [Ke69], who proved it is true if f is measurable.
Erdős [Er81b] wrote "if it were my problem I would offer $500 for it".
Laczkovich [La84] solved it in the affirmative.
-/
theorem erdos_problem_1125 :
    ∀ f : ℝ → ℝ,
    (∀ x : ℝ, ∀ h : ℝ, h > 0 → 2 * f x ≤ f (x + h) + f (x + 2 * h)) →
    Monotone f ∨ Antitone f :=
  sorry
