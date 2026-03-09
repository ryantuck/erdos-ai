import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #1141 [Va99,1.6]:

Are there infinitely many n such that n - k² is prime for all k with
gcd(n, k) = 1 and k² < n?

The list of n satisfying this property is A214583 in the OEIS. The largest
known such n is 1722.
-/
theorem erdos_problem_1141 :
    Set.Infinite {n : ℕ | ∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → Nat.Prime (n - k ^ 2)} :=
  sorry
