import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Real.Basic

open Finset

/-- The sum of squared consecutive gaps in a sorted list of natural numbers. -/
def sumSquaredGaps : List ℕ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (b - a) ^ 2 + sumSquaredGaps (b :: rest)

/-- The totatives of n listed in increasing order: all m with 1 ≤ m < n
    and gcd(m, n) = 1. -/
def sortedTotatives (n : ℕ) : List ℕ :=
  ((Finset.range n).filter (fun m => 0 < m ∧ Nat.Coprime m n)).sort (· ≤ ·)

/--
Erdős Problem #220 [Er40, Er55c, Er57, Er61, Er65b, Er73, Er79, ErGr80, Er81k, Er85c]:

Let n ≥ 1 and A = {a₁ < ⋯ < a_{φ(n)}} = {1 ≤ m < n : gcd(m,n) = 1} be the
totatives of n listed in increasing order. Is it true that

  ∑_{1 ≤ k < φ(n)} (a_{k+1} - aₖ)² ≪ n² / φ(n)?

The answer is yes, as proved by Montgomery and Vaughan [MoVa86], who showed
the more general result that for any γ ≥ 1,

  ∑_{1 ≤ k < φ(n)} (a_{k+1} - aₖ)^γ ≪ n^γ / φ(n)^{γ-1}.
-/
theorem erdos_problem_220 :
    ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, 1 ≤ n →
      (sumSquaredGaps (sortedTotatives n) : ℝ) ≤ C * (n : ℝ) ^ 2 / (Nat.totient n : ℝ) :=
  sorry
