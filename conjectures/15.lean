import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Nat

/--
Erdős's conjecture on alternating sum of primes (Problem #15):
The series ∑_{n=1}^∞ (-1)^n * n / p_n converges, where p_n is the n-th prime.
-/
theorem erdos_problem_15_conjecture :
  Summable (fun k : ℕ => ((-1 : ℝ) ^ (k + 1) * (k + 1 : ℝ)) / (nth Nat.Prime k : ℝ)) :=
sorry
