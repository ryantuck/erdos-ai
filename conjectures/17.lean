import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Cofinite

open Filter

/--
A prime `p` is a **cluster prime** if every even number `n` with `2 ≤ n` and
`n ≤ p - 3` can be written as a difference `q₁ - q₂` of two primes `q₁, q₂ ≤ p`.
-/
def IsClusterPrime (p : ℕ) : Prop :=
  p.Prime ∧
    ∀ n : ℕ, 2 ≤ n → n ≤ p - 3 → Even n →
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₁ ≤ p ∧ q₂ ≤ p ∧ n = q₁ - q₂

/--
Erdős Problem #17 [Er95, p.172]:

Are there infinitely many primes `p` such that every even number `n ≤ p - 3`
can be written as a difference of two primes `q₁ - q₂` where `q₁, q₂ ≤ p`?
Such primes are called cluster primes. The first prime without this property
is 97.

Blecksmith, Erdős, and Selfridge proved that the number of cluster primes up
to x is ≪_A x/(log x)^A for every A > 0. Elsholtz improved this to
≪ x · exp(-c(log log x)²) for every c < 1/8.
-/
theorem erdos_problem_17 : {p : ℕ | IsClusterPrime p}.Infinite :=
  sorry
