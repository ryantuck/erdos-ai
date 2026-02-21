import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #279

Let k ≥ 3. Is there a choice of congruence classes a_p (mod p) for every prime p
such that all sufficiently large integers can be written as a_p + t·p for some
prime p and integer t ≥ k?

Even the case k = 3 seems difficult. The conjecture may hold with the primes
replaced by any set A ⊆ ℕ with |A ∩ [1,N]| ≫ N/log N and
∑_{n ∈ A, n ≤ N} 1/n - log log N → ∞.

For k = 1 or k = 2, any set A with ∑_{n ∈ A} 1/n = ∞ has this property.
-/

/--
Erdős Problem #279 [ErGr80, p.29]:

For every k ≥ 3, there exists a choice of congruence classes a_p (mod p) for
every prime p such that all sufficiently large integers n can be represented as
n = a_p + t·p for some prime p and integer t ≥ k.
-/
theorem erdos_problem_279 (k : ℕ) (hk : 3 ≤ k) :
    ∃ a : ℕ → ℤ,
      ∃ N₀ : ℤ, ∀ n : ℤ, N₀ ≤ n →
        ∃ p : ℕ, Nat.Prime p ∧
          ∃ t : ℤ, (k : ℤ) ≤ t ∧ n = a p + t * (p : ℤ) :=
  sorry
