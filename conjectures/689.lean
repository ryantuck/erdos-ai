import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic

open Finset

/--
Erdős Problem #689 [Er79d]:

Let n be sufficiently large. Is there some choice of congruence class aₚ for
all primes 2 ≤ p ≤ n such that every integer in [1, n] satisfies at least two
of the congruences ≡ aₚ (mod p)?
-/
theorem erdos_problem_689 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ a : ℕ → ℕ,
        ∀ m : ℕ, 1 ≤ m → m ≤ n →
          2 ≤ ({p ∈ (Finset.range (n + 1)) | Nat.Prime p ∧ m % p = a p}.card) :=
  sorry
