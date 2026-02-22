import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Finset BigOperators

noncomputable section

/-!
# Erdős Problem #783

Fix some constant C > 0 and let N be large. Let A ⊆ {2, …, N} be such that
(a, b) = 1 for all a ≠ b ∈ A and ∑_{n ∈ A} 1/n ≤ C.

What choice of such an A minimises the number of integers m ≤ N not divisible
by any a ∈ A?

Erdős suggests the optimal set is consecutive largest primes up to N.
Tao conjectures the minimum is (ρ(eᶜ) + o(1))N where ρ is the Dickman function.
-/

/-- The Dickman rho function, the unique continuous function ρ : ℝ → ℝ satisfying
    ρ(u) = 1 for 0 ≤ u ≤ 1 and u·ρ'(u) = -ρ(u-1) for u > 1. -/
noncomputable def dickmanRho : ℝ → ℝ := sorry

/-- Count of integers in {1, …, N} not divisible by any element of A. -/
def unsievedCount (N : ℕ) (A : Finset ℕ) : ℕ :=
  ((Finset.range N).image (· + 1)).filter
    (fun m => ∀ a ∈ A, ¬(a ∣ m)) |>.card

/--
Erdős Problem #783 (Tao's formulation):

For any C > 0, the minimum number of integers in {1, …, N} not divisible by
any element of a pairwise coprime set A ⊆ {2, …, N} with ∑_{a ∈ A} 1/a ≤ C
is asymptotically ρ(eᶜ) · N, where ρ is the Dickman function.

That is, for every ε > 0 and large enough N:
(1) There exists a valid A with unsieved count ≤ (ρ(eᶜ) + ε) · N.
(2) Every valid A has unsieved count ≥ (ρ(eᶜ) - ε) · N.
-/
theorem erdos_problem_783 (C : ℝ) (hC : C > 0) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (∃ (A : Finset ℕ),
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ N) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) ∧
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ) ≤ C) ∧
        (unsievedCount N A : ℝ) ≤ (dickmanRho (Real.exp C) + ε) * ↑N) ∧
      (∀ (A : Finset ℕ),
        (∀ a ∈ A, 2 ≤ a ∧ a ≤ N) →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → Nat.Coprime a b) →
        (∑ a ∈ A, (1 : ℝ) / (a : ℝ) ≤ C) →
        (dickmanRho (Real.exp C) - ε) * ↑N ≤ (unsievedCount N A : ℝ)) :=
  sorry

end
