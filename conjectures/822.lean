import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset Filter Classical

noncomputable section

/-!
# Erdős Problem #822

Does the set of integers of the form $n + \phi(n)$ have positive (lower) density?

A similar question can be asked for $n + \sigma(n)$, where $\sigma$ is the sum of
divisors function.

This is true, and was proved by Gabdullin, Iudelevich, and Luca [GIL24].
-/

/-- The set of positive integers that can be written as n + φ(n) for some n. -/
def totientShiftImage : Set ℕ :=
  {m : ℕ | ∃ n : ℕ, 0 < n ∧ m = n + Nat.totient n}

/--
Erdős Problem #822 [Er74b]:

The set of integers of the form n + φ(n) has positive lower density, i.e.,
there exists δ > 0 such that for all sufficiently large N,
|{m ≤ N : m = n + φ(n) for some n}| ≥ δ · N.
-/
theorem erdos_problem_822 :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ (N : ℕ) in atTop,
        δ * (N : ℝ) ≤ (((Finset.Icc 1 N).filter (· ∈ totientShiftImage)).card : ℝ) :=
  sorry

end
