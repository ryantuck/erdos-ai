import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #1081

Let A(x) count the number of n ≤ x which are the sum of two squarefull numbers
(a number m is squarefull if p ∣ m implies p² ∣ m). Is it true that

  A(x) ~ c · x / √(log x)

for some c > 0?

This was disproved by Odoni [Od81].
-/

/-- A natural number is squarefull (powerful) if it is positive and for every
    prime p dividing it, p² also divides it. -/
def Nat.IsSquarefull (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p ^ 2 ∣ m

/-- A natural number is expressible as the sum of two squarefull numbers. -/
def IsSumOfTwoSquarefull (n : ℕ) : Prop :=
  ∃ a b : ℕ, a.IsSquarefull ∧ b.IsSquarefull ∧ n = a + b

/-- A(x): the count of natural numbers n in [1, x] that are sums of two
    squarefull numbers. -/
noncomputable def erdos1081_A (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => IsSumOfTwoSquarefull n)).card

/--
Erdős Problem #1081 [Er76e] (DISPROVED):

There exists c > 0 such that A(x) ~ c · x / √(log x), i.e.,
  A(x) · √(log x) / x → c as x → ∞.

This was disproved by Odoni [Od81].
-/
theorem erdos_problem_1081 :
    ∃ c : ℝ, c > 0 ∧
    Tendsto (fun x : ℕ =>
      (erdos1081_A x : ℝ) * Real.sqrt (Real.log (x : ℝ)) / (x : ℝ))
      atTop (nhds c) :=
  sorry

end
