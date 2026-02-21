import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Classical Finset

/-!
# Erdős Problem #280 (Disproved)

Let n₁ < n₂ < ⋯ be an infinite sequence of integers with associated residue
classes aₖ (mod nₖ), such that for some ε > 0 we have nₖ > (1+ε)k log k for
all k ≥ 1. Erdős and Graham conjectured that

  #{m < nₖ : m ≢ aᵢ (mod nᵢ) for 1 ≤ i ≤ k} ≠ o(k).

This was disproved by Cambie, who observed that taking nₖ = 2^k and
aₖ = 2^(k-1) + 1 for k ≥ 1 gives a trivial counterexample: the only m
not in any congruence class is 1, so the count is 1 for all k.

We formalize the negation (the true statement): there exist such sequences
where the sieve count is o(k).
-/

/-- The count of integers m < n(k) that avoid all congruence classes a(i) mod n(i)
    for 1 ≤ i ≤ k. -/
noncomputable def sieveCount (n a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range (n k)).filter fun m =>
    ∀ i ∈ Finset.Icc 1 k, ¬(m ≡ a i [MOD n i])).card

/--
Erdős Problem #280 (DISPROVED) [ErGr80, p.29]:

There exist a strictly increasing sequence n₁ < n₂ < ⋯ of positive integers
and associated residue classes aₖ (mod nₖ), with nₖ > (1+ε)k log k for some
ε > 0 and all k ≥ 1, such that the sieve count
  #{m < nₖ : m ≢ aᵢ (mod nᵢ) for 1 ≤ i ≤ k}
is o(k) as k → ∞.
-/
theorem erdos_problem_280 :
    ∃ (n : ℕ → ℕ) (a : ℕ → ℕ) (ε : ℝ),
      0 < ε ∧
      StrictMono n ∧
      (∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * ↑k * Real.log ↑k) ∧
      ∀ c : ℝ, 0 < c →
        ∃ K : ℕ, ∀ k, K ≤ k →
          (sieveCount n a k : ℝ) < c * ↑k :=
  sorry
