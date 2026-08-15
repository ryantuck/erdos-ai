import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

/--
Erdős Problem #1141 [Va99,1.6]:

**Are there infinitely many n such that n - k² is prime for all k with
gcd(n, k) = 1 and k² < n?**

Status: OPEN (as of 2026-03-09; metadata mirror dated 2026-04-11 reports "disproved (Lean)"
— status resolution deferred pending external verification).

The list of n satisfying this property is A214583 in the OEIS. The largest known such n
is 1722. ChatGPT and Tang showed that the number of such n in [1,N] is at most N^(1/2+o(1)).

Note: Va99 incorrectly asked whether 968 is the largest; 968 - 9 = 7·137 is composite.
Related problems: #1140, #1142.
-/
theorem erdos_problem_1141 :
    answer(sorry) ↔ Set.Infinite {n : ℕ | ∀ k : ℕ, k ^ 2 < n → Nat.Coprime n k → Nat.Prime (n - k ^ 2)} :=
  sorry
