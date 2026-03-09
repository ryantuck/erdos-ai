import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic

open Nat

/--
Erdős Problem #376 [ErGr80,p.71]:

Are there infinitely many $n$ such that $\binom{2n}{n}$ is coprime to $105$?

Since $105 = 3 \times 5 \times 7$, this asks whether $\gcd(\binom{2n}{n}, 105) = 1$
for infinitely many $n$. By Kummer's theorem this is equivalent to asking whether
there are infinitely many $n$ whose base-3 digits are all in {0,1}, base-5 digits
are all in {0,1,2}, and base-7 digits are all in {0,1,2,3}.

Erdős, Graham, Ruzsa, and Straus proved the analogous result for any two odd primes.
Graham offered $1000 for a solution.
-/
theorem erdos_problem_376 :
    Set.Infinite {n : ℕ | Nat.Coprime (Nat.choose (2 * n) n) 105} :=
  sorry
