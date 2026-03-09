import Mathlib.Data.Nat.Prime.Basic

open Nat

/--
Erdős Problem #219 [Er57, Er61, Er65b, Er80c, Er81, Er83]:

Are there arbitrarily long arithmetic progressions of primes?

That is, for every k, there exist a and d > 0 such that
a, a + d, a + 2d, ..., a + (k-1)d are all prime.

The answer is yes, proved by Green and Tao (2008).
-/
theorem erdos_problem_219 :
    ∀ k : ℕ, ∃ a d : ℕ, 0 < d ∧
      ∀ i : ℕ, i < k → Nat.Prime (a + i * d) :=
  sorry
