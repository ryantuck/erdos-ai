import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

/--
Erdős Problem #728 [EGRS75]:

Let C > 0 and ε > 0 be sufficiently small. Are there infinitely many integers
a, b, n with a ≥ εn and b ≥ εn such that a! b! ∣ n!(a+b-n)! and a+b > n + C log n?

A question of Erdős, Graham, Ruzsa, and Straus. Proved by Barreto and ChatGPT-5.2,
who showed that for any 0 < C₁ < C₂, there are infinitely many a, b, n with
b = n/2, a = n/2 + O(log n), and C₁ log n < a + b - n < C₂ log n such that
a! b! ∣ n!(a+b-n)!.
-/
theorem erdos_problem_728 :
    ∃ C : ℝ, 0 < C ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ N : ℕ, ∃ a b n : ℕ, n ≥ N ∧
        (a : ℝ) ≥ ε * (n : ℝ) ∧
        (b : ℝ) ≥ ε * (n : ℝ) ∧
        n ≤ a + b ∧
        a.factorial * b.factorial ∣ n.factorial * (a + b - n).factorial ∧
        ((a : ℝ) + (b : ℝ)) > (n : ℝ) + C * Real.log (n : ℝ) :=
  sorry
