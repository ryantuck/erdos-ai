import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset

noncomputable section

/--
The primorial of order k: the product of the first k primes (0-indexed).
primorial k = p₁ · p₂ · … · pₖ where pᵢ is the i-th prime.
-/
def primorial (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, nth Nat.Prime i

/--
Erdős Problem #891 [ErSe67, p.430]:

Let 2 = p₁ < p₂ < ⋯ be the primes and k ≥ 2. Is it true that, for all
sufficiently large n, there must exist an integer in [n, n + p₁⋯pₖ) with
more than k prime factors (counted with multiplicity)?

This is unknown even for k = 2: is it true that in every interval of 6
sufficiently large consecutive integers there must exist one with at least
3 prime factors?
-/
theorem erdos_problem_891 (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ m : ℕ, n ≤ m ∧ m < n + primorial k ∧ k < m.primeFactorsList.length :=
  sorry

end
