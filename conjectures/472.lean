import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Erdős Problem #472

Given some initial finite sequence of primes q₁ < ⋯ < qₘ, extend it so that
q_{n+1} is the smallest prime of the form qₙ + qᵢ - 1 for n ≥ m. Is there an
initial starting sequence so that the resulting sequence is infinite?

A problem due to Ulam. For example if we begin with 3, 5 then the sequence
continues 3, 5, 7, 11, 13, 17, …. It is possible that this sequence is infinite.
-/

/-- A sequence q : ℕ → ℕ is an Erdős-Ulam sequence (Problem 472) with initial
    segment of length m if all terms are prime and for each n with n + 1 ≥ m,
    q(n + 1) is the smallest prime of the form q(n) + q(i) - 1 for i ≤ n. -/
def IsErdos472Sequence (q : ℕ → ℕ) (m : ℕ) : Prop :=
  (∀ n, Nat.Prime (q n)) ∧
  StrictMono q ∧
  ∀ n, m ≤ n + 1 →
    (∃ i, i ≤ n ∧ q (n + 1) = q n + q i - 1) ∧
    (∀ i, i ≤ n → Nat.Prime (q n + q i - 1) → q (n + 1) ≤ q n + q i - 1)

/--
Erdős Problem #472 (Open):
There exists an initial finite sequence of primes such that the Erdős-Ulam
extension process produces an infinite sequence. That is, there exists an
infinite sequence where each term after the initial segment is the smallest
prime of the form q(n) + q(i) - 1.
-/
theorem erdos_problem_472 :
    ∃ (q : ℕ → ℕ) (m : ℕ), 0 < m ∧ IsErdos472Sequence q m :=
  sorry
