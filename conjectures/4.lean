import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

open Real Nat

/--
Erdős's conjecture on large prime gaps (Problem #4).
There are infinitely many n such that
p_{n+1} - p_n > C * (log n * log (log n) * log (log (log (log n)))) / (log (log (log n)))^2.
-/
theorem erdos_problem_4_conjecture :
  ∀ C : ℝ, C > 0 →
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
  let p_n := nth Nat.Prime n
  let p_succ_n := nth Nat.Prime (n + 1)
  (p_succ_n : ℝ) - (p_n : ℝ) >
    C * (log (n : ℝ) * log (log (n : ℝ)) * log (log (log (log (n : ℝ))))) / (log (log (log (n : ℝ)))) ^ 2 :=
sorry
