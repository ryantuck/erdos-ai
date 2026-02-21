import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

noncomputable section

/-- The largest prime factor of a natural number n. Returns 0 if n ≤ 1. -/
def largestPrimeFactor372 (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-!
# Erdős Problem #372

Let P(n) denote the largest prime factor of n. There are infinitely many n
such that P(n) > P(n+1) > P(n+2).

Conjectured by Erdős and Pomerance [ErPo78], who proved the analogous result
for P(n) < P(n+1) < P(n+2). Solved by Balog [Ba01], who proved that this is
true for ≫ √x many n ≤ x (for all large x). Balog suggests the natural
conjecture that the density of such n is 1/6.
-/

/--
Erdős Problem #372 [ErPo78] [ErGr80] [Er85c]:

There are infinitely many n such that P(n) > P(n+1) > P(n+2), where
P(n) denotes the largest prime factor of n.
-/
theorem erdos_problem_372 :
    Set.Infinite {n : ℕ |
      largestPrimeFactor372 n > largestPrimeFactor372 (n + 1) ∧
      largestPrimeFactor372 (n + 1) > largestPrimeFactor372 (n + 2)} :=
  sorry

end
