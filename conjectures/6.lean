import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth

open Nat

/--
Erdős's conjecture on increasing prime gaps (Problem #6).
There are infinitely many n such that p_{n+1} - p_n < p_{n+2} - p_{n+1} < p_{n+3} - p_{n+2}.
This is formalized as: for every N, there exists n ≥ N such that the consecutive prime gaps
starting at n are strictly increasing.
-/
theorem erdos_problem_6_conjecture :
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
  let p_n := nth Nat.Prime n
  let p_succ_n := nth Nat.Prime (n + 1)
  let p_succ2_n := nth Nat.Prime (n + 2)
  let p_succ3_n := nth Nat.Prime (n + 3)
  let d_n := p_succ_n - p_n
  let d_succ_n := p_succ2_n - p_succ_n
  let d_succ2_n := p_succ3_n - p_succ2_n
  d_n < d_succ_n ∧ d_succ_n < d_succ2_n :=
sorry
