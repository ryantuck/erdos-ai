import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset BigOperators

/-!
# Erdős Problem #423

Let a₁ = 1 and a₂ = 2, and for k ≥ 3 choose aₖ to be the least integer > aₖ₋₁
which is the sum of at least two consecutive terms of the sequence. What is the
asymptotic behaviour of this sequence?

The sequence begins 1, 2, 3, 5, 6, 8, 10, 11, ... (OEIS A005243).

Asked by Hofstadter (Erdős says Hofstadter was inspired by a similar question of Ulam).
Bolan and Tang have independently proved that aₙ - n is nondecreasing and unbounded,
so there are infinitely many integers not appearing in the sequence.
-/

/-- `IsConsecutiveBlockSum a k m` means that `m` equals the sum of at least two
    consecutive terms of the sequence `a`, using indices from {1, ..., k - 1}.
    That is, there exist i, j with 1 ≤ i, i + 1 ≤ j, j ≤ k - 1 such that
    m = a(i) + a(i+1) + ... + a(j). -/
def IsConsecutiveBlockSum (a : ℕ → ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ i j : ℕ, 1 ≤ i ∧ i + 1 ≤ j ∧ j + 1 ≤ k ∧
    m = ∑ l ∈ Finset.Icc i j, a l

/-- The Hofstadter sequence (OEIS A005243): a(1) = 1, a(2) = 2, and for k ≥ 3,
    a(k) is the least integer > a(k-1) that equals the sum of at least two
    consecutive terms from {a(1), ..., a(k-1)}. -/
def IsHofstadterSeq (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 2 ∧
  ∀ k : ℕ, 3 ≤ k →
    IsConsecutiveBlockSum a k (a k) ∧
    a (k - 1) < a k ∧
    ∀ m : ℕ, a (k - 1) < m → m < a k → ¬IsConsecutiveBlockSum a k m

/--
Erdős Problem #423 [Er77c, p.71; ErGr80, p.83]:

Let a(1) = 1, a(2) = 2, and for k ≥ 3 let a(k) be the least integer greater
than a(k-1) that is a sum of at least two consecutive terms of the sequence.
Then a(n) - n → ∞ as n → ∞.

Equivalently, there are infinitely many positive integers not in the range of a.
This was proved independently by Bolan and Tang. The full asymptotic behaviour
of the sequence remains an open question.
-/
theorem erdos_problem_423 :
    ∀ a : ℕ → ℕ, IsHofstadterSeq a →
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M + n ≤ a n :=
  sorry
