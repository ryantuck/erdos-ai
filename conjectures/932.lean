import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Nth

/--
The n-th prime number (0-indexed), i.e., nthPrime 0 = 2, nthPrime 1 = 3, etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
All prime factors of n are strictly less than b.
-/
def AllPrimeFactorsLt (n b : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p < b

/--
Erdős Problem #932 [Er76d]:

Let p_k denote the k-th prime. For infinitely many r there are at least two
integers p_r < n < p_{r+1} all of whose prime factors are < p_{r+1} - p_r.

Erdős thought this was true but that there are very few such r. He could show
that the density of r such that at least one such n exists is 0.
-/
theorem erdos_problem_932 :
    Set.Infinite {r : ℕ | ∃ n₁ n₂ : ℕ,
      n₁ ≠ n₂ ∧
      nthPrime r < n₁ ∧ n₁ < nthPrime (r + 1) ∧
      nthPrime r < n₂ ∧ n₂ < nthPrime (r + 1) ∧
      AllPrimeFactorsLt n₁ (nthPrime (r + 1) - nthPrime r) ∧
      AllPrimeFactorsLt n₂ (nthPrime (r + 1) - nthPrime r)} :=
  sorry
