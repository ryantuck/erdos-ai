import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Real

noncomputable section

/-!
# Erdős Problem #784

Let C > 0. Does there exist a c > 0 (depending on C) such that, for all
sufficiently large x, if A ⊆ {2, …, x} has ∑_{a ∈ A} 1/a ≤ C then

  #{m ≤ x : a ∤ m for all a ∈ A} ≫ x / (log x)^c ?

Note: as observed in the comments, the assumption 1 ∉ A is intended (otherwise
A = {1} gives a trivial counterexample for C ≥ 1).

This problem has been resolved:
- For 0 < C ≤ 1: YES (lower bound by Ruzsa [Ru82], upper bound by Saias [Sa98]).
- For C > 1: NO (Ruzsa showed H_C(x) = x^{e^{1-C} + o(1)},
  improved by Weingartner [We25] to H_C(x) ≍ x^{e^{1-C}} / log x).

https://www.erdosproblems.com/784

Tags: number theory
-/

/--
Erdős Problem #784:

For every C > 0, does there exist c > 0 and a constant K > 0 such that for all
sufficiently large x, every A ⊆ {2, …, x} with ∑_{a ∈ A} 1/a ≤ C satisfies

  #{m ≤ x : a ∤ m for all a ∈ A} ≥ K · x / (log x)^c ?

(Resolved: true for 0 < C ≤ 1, false for C > 1.)
-/
theorem erdos_problem_784 :
    ∀ C : ℝ, C > 0 →
    ∃ c : ℝ, c > 0 ∧
    ∃ K : ℝ, K > 0 ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      ∀ A : Finset ℕ,
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ x) →
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ)) ≤ C →
        (((Finset.Icc 1 x).filter (fun m => ∀ a ∈ A, ¬(a ∣ m))).card : ℝ) ≥
          K * (x : ℝ) / (Real.log (x : ℝ)) ^ c :=
  sorry

end
