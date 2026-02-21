import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators Filter

/--
A valid representation of n! as a product of n positive integers in
non-decreasing order.
-/
def IsFactorialRepr (n : ℕ) (f : Fin n → ℕ) : Prop :=
  (∀ i, 0 < f i) ∧ Monotone f ∧ ∏ i, f i = n.factorial

/--
t(n) is the maximal value of the smallest factor in any representation of n!
as a product of n positive integers in non-decreasing order.
-/
noncomputable def erdos391_t (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ f : Fin n → ℕ, IsFactorialRepr n f ∧ ∀ i, k ≤ f i}

/--
Erdős Problem #391 (Part 1):
Let t(n) be maximal such that n! = a₁⋯aₙ with t(n) = a₁ ≤ ⋯ ≤ aₙ.
The limit of t(n)/n as n → ∞ equals 1/e.
-/
theorem erdos_problem_391_part1 :
    Tendsto (fun n : ℕ => (erdos391_t n : ℝ) / (n : ℝ))
      atTop (nhds (1 / Real.exp 1)) :=
  sorry

/--
Erdős Problem #391 (Part 2):
There exists a constant c > 0 such that t(n)/n ≤ 1/e - c/log(n) for
infinitely many n.
-/
theorem erdos_problem_391_part2 :
    ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      (erdos391_t n : ℝ) / (n : ℝ) ≤ 1 / Real.exp 1 - c / Real.log (n : ℝ) :=
  sorry
