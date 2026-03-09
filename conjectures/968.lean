import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Classical

noncomputable section

/-- The n-th prime number (0-indexed): nthPrime 0 = 2, nthPrime 1 = 3, etc. -/
def nthPrime968 (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- u_n = p_n / n, the ratio of the n-th prime to its index. -/
def u968 (n : ℕ) : ℝ := (nthPrime968 n : ℝ) / (n : ℝ)

/--
Erdős Problem #968 [Er65b]:

Let u_n = p_n / n, where p_n is the n-th prime. Does the set of n such that
u_n < u_{n+1} have positive density?

Erdős and Prachar [ErPr61] proved that
  ∑_{p_n < x} |u_{n+1} - u_n| ≍ (log x)²
and that the set of n such that u_n > u_{n+1} has positive density.

Erdős also asks whether u_n < u_{n+1} < u_{n+2} or u_n > u_{n+1} > u_{n+2}
have infinitely many solutions.
-/
theorem erdos_problem_968 :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ (N : ℕ) in atTop,
        δ * (N : ℝ) ≤ (((Finset.Icc 1 N).filter (fun n => u968 n < u968 (n + 1))).card : ℝ) :=
  sorry

end
