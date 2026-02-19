import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

open Nat

/--
Erdős's conjecture on odd integers (Problem #11):
Is every large odd integer n the sum of a squarefree number and a power of 2?
-/
theorem erdos_problem_11_conjecture :
  ∃ N, ∀ n ≥ N, Odd n → ∃ s k, Squarefree s ∧ n = s + 2^k :=
sorry
