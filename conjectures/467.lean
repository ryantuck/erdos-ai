import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic

/--
Erdős Problem #467 [ErGr80, p.93]:

For all sufficiently large x, there exists a choice of congruence classes
a_p for every prime p ≤ x, and a decomposition of the set of primes ≤ x
into two non-empty sets A and B, such that for every n < x, there exist
some p ∈ A and q ∈ B with n ≡ a_p (mod p) and n ≡ a_q (mod q).

The note on the website indicates the original source [ErGr80] is ambiguous
about the quantifiers; this formalises the most natural interpretation.
-/
theorem erdos_problem_467 :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      ∃ (a : ℕ → ℕ) (A : Finset ℕ),
        let P := (Finset.range (x + 1)).filter Nat.Prime
        A ⊆ P ∧
        A.Nonempty ∧
        (P \ A).Nonempty ∧
        ∀ n : ℕ, n < x →
          (∃ p ∈ A, n % p = a p % p) ∧
          (∃ q ∈ P \ A, n % q = a q % q) :=
  sorry
