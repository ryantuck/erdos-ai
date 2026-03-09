import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
Erdős Problem #855 [Er61, Er65b, Er82e, Er85c]:

If π(x) counts the number of primes in [1,x] then is it true that (for large x and y)
  π(x+y) ≤ π(x) + π(y)?

Commonly known as the second Hardy–Littlewood conjecture. This is probably false, since
Hensley and Richards have shown it is incompatible with the prime tuples conjecture.

Tags: number theory, primes
-/
theorem erdos_problem_855 :
    ∃ N₀ : ℕ, ∀ x y : ℕ, x ≥ N₀ → y ≥ N₀ →
      Nat.primeCounting (x + y) ≤ Nat.primeCounting x + Nat.primeCounting y :=
  sorry
