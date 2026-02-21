import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators Filter Real

/-!
# Erdős Problem #297

Let N ≥ 1. How many A ⊆ {1, ..., N} are there such that ∑_{n ∈ A} 1/n = 1?

It was not even known for a long time whether this is 2^{cN} for some c < 1 or
2^{(1+o(1))N}. In fact the former is true, and the correct value of c is now known.

Steinerberger [St24] proved the count is at most 2^{0.93N}. Independently,
Liu and Sawhney [LiSa24] gave both upper and lower bounds, proving that the
count is 2^{(0.91...+o(1))N}, where 0.91... is an explicit number defined as
the solution to a certain integral equation. Again independently, the same
asymptotic was proved by Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte [CFHMPSV24].
-/

/-- Count of subsets A ⊆ {1, ..., N} such that ∑_{n ∈ A} 1/n = 1. -/
noncomputable def unitFractionSubsetCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter fun (A : Finset ℕ) =>
    (A.sum fun n => (1 : ℚ) / (n : ℚ)) = 1).card

/--
Erdős Problem #297 [ErGr80, p.36] — SOLVED

There exists a constant c ∈ (0, 1) such that the number of subsets
A ⊆ {1, ..., N} with ∑_{n ∈ A} 1/n = 1 is 2^{(c+o(1))N}.

Equivalently, log₂(count(N)) / N → c as N → ∞.
-/
theorem erdos_problem_297 :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      Tendsto (fun N : ℕ =>
        Real.log (unitFractionSubsetCount N : ℝ) / (Real.log 2 * (N : ℝ)))
        atTop (nhds c) :=
  sorry
