import Mathlib.NumberTheory.Divisors

open Nat

/--
The number-of-divisors function τ(n) = |{d : d ∣ n}|.
-/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/--
Erdős Problem #946 [ErMi52, Er85e]:

Are there infinitely many n such that τ(n) = τ(n+1), where τ is the divisor
function?

A problem of Erdős and Mirsky. Heath-Brown proved this in the affirmative,
showing that the number of such n ≤ x is ≫ x/(log x)^7. Hildebrand improved
the lower bound to ≫ x/(log log x)^3.
-/
theorem erdos_problem_946 : Set.Infinite {n : ℕ | tau n = tau (n + 1)} :=
  sorry
