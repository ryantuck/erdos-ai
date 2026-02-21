import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #240

Is there an infinite set of primes P such that if {a₁ < a₂ < ⋯} is the set of
positive integers divisible only by primes in P, then lim(a_{i+1} - a_i) = ∞?

Originally asked to Erdős by Wintner. The answer is yes for finite sets of primes,
which follows from a theorem of Pólya [Po18].

Tijdeman [Ti73] resolved this question, proving that for any ε > 0, there exists
an infinite set of primes P such that a_{i+1} - a_i ≫ a_i^{1-ε}.
-/

/-- The set of positive integers all of whose prime factors lie in P. -/
def smoothNumbers (P : Set ℕ) : Set ℕ :=
  {n : ℕ | 0 < n ∧ ∀ q : ℕ, Nat.Prime q → q ∣ n → q ∈ P}

/--
Erdős Problem #240 [Er61, Er65b]:
There exists an infinite set of primes P such that if {a₁ < a₂ < ⋯} is the
set of positive integers divisible only by primes in P (the P-smooth numbers),
then the consecutive gaps a_{i+1} - a_i tend to infinity.

Equivalently: for every bound B, only finitely many P-smooth numbers n have
another P-smooth number within distance B above them.

Proved by Tijdeman [Ti73].
-/
theorem erdos_problem_240 :
    ∃ P : Set ℕ, Set.Infinite P ∧ (∀ p ∈ P, Nat.Prime p) ∧
      ∀ B : ℕ, Set.Finite {n : ℕ | n ∈ smoothNumbers P ∧
        ∃ m ∈ smoothNumbers P, n < m ∧ m ≤ n + B} :=
  sorry
