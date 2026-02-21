import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Finset Filter

/-!
# Erdős Problem #440

Let A = {a₁ < a₂ < ⋯} ⊆ ℕ be infinite and let A(x) count the number of
indices i for which lcm(aᵢ, aᵢ₊₁) ≤ x. Is it true that A(x) ≪ x^{1/2}?

How large can liminf A(x)/x^{1/2} be?

Taking A = ℕ shows that liminf A(x)/x^{1/2} = 1 is possible. Erdős and
Szemerédi [ErSz80] proved that it is always ≤ 1.

Tao proved that A(x) ≪ x^{1/2}. van Doorn proved that
A(x) ≤ (c + o(1))x^{1/2} where c = ∑_{n ≥ 1} 1/(n^{1/2}(n+1)) ≈ 1.86.
This was already proved by Erdős and Szemerédi, who showed this constant
is best possible.
-/

/-- For a strictly increasing sequence a : ℕ → ℕ and a bound x, count the
number of indices i such that lcm(a(i), a(i+1)) ≤ x. -/
def lcmPairCount (a : ℕ → ℕ) (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun i => Nat.lcm (a i) (a (i + 1)) ≤ x)).card

/-- Erdős Problem #440, part 1 (PROVED):
For any strictly increasing sequence a : ℕ → ℕ, the counting function
A(x) = #{i : lcm(a(i), a(i+1)) ≤ x} satisfies A(x) = O(√x).

Proved by Tao; the sharp constant was determined by Erdős–Szemerédi [ErSz80]. -/
theorem erdos_problem_440 (a : ℕ → ℕ) (ha : StrictMono a) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop,
    (lcmPairCount a x : ℝ) ≤ C * Real.sqrt (x : ℝ) :=
  sorry

/-- Erdős Problem #440, liminf bound (PROVED):
For any strictly increasing sequence a : ℕ → ℕ, there are infinitely many x
such that A(x)/√x is close to at most 1. That is, liminf A(x)/√x ≤ 1.
This bound is sharp: A = ℕ achieves equality.

Proved by Erdős and Szemerédi [ErSz80]. -/
theorem erdos_problem_440_liminf (a : ℕ → ℕ) (ha : StrictMono a) :
    ∀ ε : ℝ, 0 < ε →
    ∃ᶠ x in atTop, (lcmPairCount a x : ℝ) ≤ (1 + ε) * Real.sqrt (x : ℝ) :=
  sorry
