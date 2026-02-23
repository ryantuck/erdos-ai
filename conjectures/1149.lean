import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Floor.Defs

open Finset Filter Real Classical

noncomputable section

/-!
# Erdős Problem #1149

Let α > 0 be a real number, not an integer. The density of integers n ≥ 1
for which gcd(n, ⌊n^α⌋) = 1 is 6/π².

This was proved by Bergelson and Richter [BeRi17].

Tags: number theory
-/

/--
Erdős Problem #1149 [Va99,1.34]:

Let α > 0 be a real number, not an integer. The natural density of integers
n ≥ 1 for which gcd(n, ⌊n^α⌋) = 1 equals 6/π².

The constant 6/π² = 1/ζ(2) is the "probability" that two random integers
are coprime, so this says n and ⌊n^α⌋ behave like independent random integers
with respect to coprimality when α is not an integer.
-/
theorem erdos_problem_1149 (α : ℝ) (hα_pos : 0 < α) (hα_not_int : ∀ k : ℤ, (k : ℝ) ≠ α) :
    Tendsto (fun x : ℕ =>
      (((Finset.Icc 1 x).filter (fun n =>
        Nat.Coprime n (⌊(n : ℝ) ^ α⌋₊))).card : ℝ) / (x : ℝ))
      atTop (nhds (6 / Real.pi ^ 2)) :=
  sorry

end
