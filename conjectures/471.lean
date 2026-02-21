import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #471

Given a finite set of primes Q = Q₀, define a sequence of sets Qᵢ by letting
Q_{i+1} be Qᵢ together with all primes formed by adding three distinct elements
of Qᵢ. Is there some initial choice of Q such that the Qᵢ become arbitrarily large?

A problem of Ulam. Proved by Mrazović and Kovač, and independently Alon, using
Vinogradov's theorem that every large odd integer is the sum of three distinct primes.
In particular, there exists N such that every prime > N is the sum of three distinct
smaller primes. Taking Q₀ to be all primes ≤ N, all primes eventually appear.
-/

/-- Given a set Q of natural numbers, erdos471_step Q is Q together with all
    primes that equal the sum of three distinct elements of Q. -/
def erdos471_step (Q : Set ℕ) : Set ℕ :=
  Q ∪ {p | Nat.Prime p ∧ ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
    a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ p = a + b + c}

/-- The sequence Qᵢ starting from Q₀. -/
def erdos471_seq (Q₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => Q₀
  | i + 1 => erdos471_step (erdos471_seq Q₀ i)

/--
Erdős Problem #471 (Proved):

There exists a finite set of primes Q₀ such that every prime eventually
appears in some Qᵢ. This implies the Qᵢ become arbitrarily large.
-/
theorem erdos_problem_471 :
    ∃ Q₀ : Set ℕ, Q₀.Finite ∧ (∀ p ∈ Q₀, Nat.Prime p) ∧
      ∀ p : ℕ, Nat.Prime p → ∃ i : ℕ, p ∈ erdos471_seq Q₀ i :=
  sorry
