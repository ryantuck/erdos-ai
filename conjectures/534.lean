import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #534

What is the largest possible subset A ⊆ {1, …, N} containing N such that
gcd(a, b) > 1 for all distinct a, b ∈ A?

A problem of Erdős and Graham [Er73]. They originally conjectured that the
maximum is either N/p (where p is the smallest prime factor of N) or the number
of even integers 2t ≤ N with gcd(2t, N) > 1. Ahlswede and Khachatrian found
a counterexample to this conjecture in 1992.

Erdős then gave a refined conjecture: if N = q₁^k₁ ⋯ qᵣ^kᵣ where
q₁ < ⋯ < qᵣ are distinct primes, then the maximum is achieved by taking,
for some 1 ≤ j ≤ r, all integers in [1, N] divisible by at least one element
of {2q₁, …, 2qⱼ, q₁⋯qⱼ}.

This was proved by Ahlswede and Khachatrian [AhKh96].
-/

/-- The set of prime factors of N. -/
noncomputable def erdos534_primeFactors (N : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun p => Nat.Prime p ∧ p ∣ N)

/-- The Erdős–Ahlswede–Khachatrian candidate family: for a set S of primes,
    all m ∈ {1, …, N} divisible by 2p for some p ∈ S or by ∏ p ∈ S. -/
noncomputable def erdos534_candidate (N : ℕ) (S : Finset ℕ) : Finset ℕ :=
  (Icc 1 N).filter fun m =>
    (∃ p ∈ S, (2 * p) ∣ m) ∨ (∏ p ∈ S, p) ∣ m

/--
Erdős Problem #534 [Er73], proved by Ahlswede–Khachatrian [AhKh96]:

If q₁ < ⋯ < qᵣ are the distinct prime factors of N ≥ 2, then the maximum size
of a subset A ⊆ {1, …, N} containing N with gcd(a, b) > 1 for all distinct
a, b ∈ A is achieved by the candidate family for some initial segment
{q₁, …, qⱼ} of the prime factors.
-/
theorem erdos_problem_534 (N : ℕ) (hN : 2 ≤ N) :
    ∃ S : Finset ℕ, S ⊆ erdos534_primeFactors N ∧ S.Nonempty ∧
      (∀ p ∈ erdos534_primeFactors N, ∀ q ∈ S, p ≤ q → p ∈ S) ∧
      N ∈ erdos534_candidate N S ∧
      (∀ a ∈ erdos534_candidate N S, ∀ b ∈ erdos534_candidate N S,
        a ≠ b → 1 < Nat.gcd a b) ∧
      (∀ A : Finset ℕ, A ⊆ Icc 1 N → N ∈ A →
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 < Nat.gcd a b) →
        A.card ≤ (erdos534_candidate N S).card) :=
  sorry

end
