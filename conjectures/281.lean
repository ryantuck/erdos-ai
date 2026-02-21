import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Classical

/-!
# Erdős Problem #281 (Proved)

Let n₁ < n₂ < ⋯ be a strictly increasing sequence of positive integers such that,
for any choice of congruence classes aᵢ (mod nᵢ), the set of integers not satisfying
any of the congruences aᵢ (mod nᵢ) has density 0.

Is it true that for every ε > 0 there exists some k such that, for every choice of
congruence classes aᵢ, the density of integers not satisfying any of the congruences
aᵢ (mod nᵢ) for 1 ≤ i ≤ k is less than ε?

This was proved to be true. The proof uses the Davenport–Erdős theorem and Rogers'
optimal sieve bound.
-/

/-- Count of integers in {0, …, N-1} not in any congruence class a(i) mod n(i) for all i. -/
noncomputable def avoidCountAll (n a : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun m =>
    ∀ i : ℕ, ¬(m ≡ a i [MOD n i])).card

/-- Count of integers in {0, …, N-1} avoiding congruences a(i) mod n(i) for i < k. -/
noncomputable def avoidCountFin (n a : ℕ → ℕ) (k N : ℕ) : ℕ :=
  ((Finset.range N).filter fun m =>
    ∀ i, i < k → ¬(m ≡ a i [MOD n i])).card

/--
Erdős Problem #281 (Proved) [ErGr80, p.29]:

Let n₁ < n₂ < ⋯ be a strictly increasing sequence of positive integers such that,
for any choice of congruence classes aᵢ (mod nᵢ), the set of integers not satisfying
any of the congruences has density 0. Then for every ε > 0 there exists some k such
that, for every choice of congruence classes aᵢ, the density of integers not satisfying
any of the congruences aᵢ (mod nᵢ) for i < k is less than ε.

The proof combines the Davenport–Erdős theorem with Rogers' optimal sieve bound.
-/
theorem erdos_problem_281
    (n : ℕ → ℕ)
    (hn_pos : ∀ i, 0 < n i)
    (hn_mono : StrictMono n)
    (h_cover : ∀ a : ℕ → ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (avoidCountAll n a N : ℝ) / (N : ℝ) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ a : ℕ → ℕ,
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → (avoidCountFin n a k N : ℝ) / (N : ℝ) < ε :=
  sorry
