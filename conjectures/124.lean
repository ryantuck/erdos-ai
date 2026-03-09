import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open scoped BigOperators
open Finset Filter

/-- P(d, k): the set of natural numbers expressible as a sum of distinct powers
    d^i with i ≥ k. These are the numbers whose base-d representation uses only
    digits 0 and 1 in positions ≥ k. -/
def powerSumSet (d : ℕ) (k : ℕ) : Set ℕ :=
  {n : ℕ | ∃ S : Finset ℕ, (∀ i ∈ S, k ≤ i) ∧ n = ∑ i ∈ S, d ^ i}

/--
Erdős Problem #124, Part 1 [Er97, Er97e] — OPEN

For any d ≥ 1 and k ≥ 0 let P(d,k) be the set of integers which are the sum of
distinct powers d^i with i ≥ k.

Let 3 ≤ d₁ < d₂ < ⋯ < d_r be integers such that ∑ 1/(dᵢ-1) ≥ 1. Can all
sufficiently large integers be written as a sum ∑ cᵢaᵢ where cᵢ ∈ {0,1} and
aᵢ ∈ P(dᵢ, 0)?

Note: since 0 ∈ P(d, k) (via the empty sum), choosing cᵢ = 0 is equivalent to
choosing aᵢ = 0, so we simply ask that N = ∑_{d ∈ ds} f(d) with f(d) ∈ P(d, 0).

A positive proof was provided by Aristotle (thanks to Alexeev); see the website
comments for details.
-/
theorem erdos_problem_124a :
    ∀ ds : Finset ℕ, (∀ d ∈ ds, 3 ≤ d) →
    1 ≤ ∑ d ∈ ds, (1 : ℝ) / ((d : ℝ) - 1) →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d 0) ∧
        N = ∑ d ∈ ds, f d :=
  sorry

/--
Erdős Problem #124, Part 2 [BEGL96] — OPEN

Under the same hypotheses as Part 1, if additionally gcd(d₁, …, d_r) = 1, then
for any k ≥ 1, all sufficiently large integers can be written as ∑ cᵢaᵢ where
cᵢ ∈ {0,1} and aᵢ ∈ P(dᵢ, k).

This was conjectured by Burr, Erdős, Graham, and Li [BEGL96], who proved it for
{3, 4, 7}.
-/
theorem erdos_problem_124b :
    ∀ ds : Finset ℕ, (∀ d ∈ ds, 3 ≤ d) →
    1 ≤ ∑ d ∈ ds, (1 : ℝ) / ((d : ℝ) - 1) →
    ds.gcd id = 1 →
    ∀ k : ℕ, 1 ≤ k →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ f : ℕ → ℕ, (∀ d ∈ ds, f d ∈ powerSumSet d k) ∧
        N = ∑ d ∈ ds, f d :=
  sorry
