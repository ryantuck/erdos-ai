import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Interval.Finset.Nat

open Finset

/-!
# Erdős Problem #290 (Proved)

Let a ≥ 1. Must there exist some b > a such that
  ∑_{a ≤ n ≤ b} 1/n = r₁/s₁  and  ∑_{a ≤ n ≤ b+1} 1/n = r₂/s₂,
with (rᵢ, sᵢ) = 1 and s₂ < s₁?

For example, ∑_{3 ≤ n ≤ 5} 1/n = 47/60 and ∑_{3 ≤ n ≤ 6} 1/n = 19/20,
and 20 < 60.

This was resolved in the affirmative by van Doorn [vD24], who proved b = b(a)
always exists and b(a) ≪ a. More precisely, b(a) < 4.374a for all a > 1,
and b(a) > a + 0.54 log a for all large a.
-/

/-- The partial harmonic sum ∑_{n=a}^{b} 1/n as a rational number. -/
def harmonicPartialSum (a b : ℕ) : ℚ :=
  (Finset.Icc a b).sum (fun n => (1 : ℚ) / ↑n)

/--
Erdős Problem #290 (Proved) [ErGr80, p.34]:

For every a ≥ 1, there exists b > a such that the denominator of
∑_{n=a}^{b+1} 1/n (in lowest terms) is strictly less than the denominator
of ∑_{n=a}^{b} 1/n (in lowest terms).
-/
theorem erdos_problem_290 :
    ∀ a : ℕ, 1 ≤ a →
    ∃ b : ℕ, a < b ∧
      (harmonicPartialSum a (b + 1)).den < (harmonicPartialSum a b).den :=
  sorry
