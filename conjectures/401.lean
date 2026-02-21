import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic

open Finset BigOperators Filter Real

noncomputable section

/-!
# Erdős Problem #401

Is there some function f(r) such that f(r) → ∞ as r → ∞, such that, for
infinitely many n, there exist a₁, a₂ with
  a₁ + a₂ > n + f(r) · log n
such that a₁! · a₂! ∣ n! · 2ⁿ · 3ⁿ · ⋯ · pᵣⁿ?

Here pᵢ denotes the i-th prime number (so p₁ = 2, p₂ = 3, …).

This has been proved in the affirmative by Barreto and Leeham.
-/

/--
Erdős Problem #401 [ErGr80, p.78]:

There exists a function f : ℕ → ℝ with f(r) → ∞ as r → ∞, such that for
every r, there are infinitely many n for which there exist a₁, a₂ ∈ ℕ with
a₁! · a₂! ∣ n! · p₁ⁿ · p₂ⁿ · ⋯ · pᵣⁿ and a₁ + a₂ > n + f(r) · log n.
-/
theorem erdos_problem_401 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ r : ℕ, {n : ℕ | ∃ a₁ a₂ : ℕ,
        (a₁.factorial * a₂.factorial) ∣
          (n.factorial * ∏ i ∈ Finset.range r, (Nat.nth Nat.Prime i) ^ n) ∧
        ((a₁ + a₂ : ℕ) : ℝ) > (n : ℝ) + f r * Real.log (n : ℝ)}.Infinite :=
  sorry

end
