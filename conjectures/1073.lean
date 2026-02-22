import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset Classical

noncomputable section

/-!
# Erdős Problem #1073

Let A(x) count the number of composite u < x such that n! + 1 ≡ 0 (mod u)
for some n. Is it true that A(x) ≤ x^{o(1)}?

Wilson's theorem states that u is prime if and only if (u-1)! + 1 ≡ 0 (mod u).

A question of Erdős raised in discussions with Hardy and Subbarao [HaSu02].
The sequence of such composite u begins 25, 121, 169, 437, ... (OEIS A256519).
-/

/-- `A x` counts the number of composite `u < x` such that `u ∣ n! + 1`
    for some `n`. -/
noncomputable def A (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun u =>
    1 < u ∧ ¬ Nat.Prime u ∧ ∃ n, u ∣ (Nat.factorial n + 1))).card

/--
Erdős Problem #1073 [HaSu02]:

Let A(x) count the number of composite u < x such that n! + 1 ≡ 0 (mod u)
for some n. Is it true that A(x) ≤ x^{o(1)}?

Formulated as: for every ε > 0, there exists x₀ such that for all x ≥ x₀,
  A(x) ≤ x^ε.
-/
theorem erdos_problem_1073 :
    ∀ ε : ℝ, ε > 0 →
    ∃ x₀ : ℕ, ∀ x : ℕ, x ≥ x₀ →
      (A x : ℝ) ≤ (x : ℝ) ^ ε :=
  sorry

end
