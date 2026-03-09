import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic

open Nat

noncomputable section

/--
The prime gap at index n: d(n) = p_{n+1} - p_n, where p_k is the k-th prime.
-/
def primeGap (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/--
Erdős Problem #6 [Er55c, Er57, Er61, Er65b, Er77c, Er79, Er79d, ErGr80, Er85c, Er90]:

Let d_n = p_{n+1} - p_n. Are there infinitely many n such that d_n < d_{n+1} < d_{n+2}?

Conjectured by Erdős and Turán. Proved by Banks, Freiberg, and
Turnage-Butterbaugh (2015) using the Maynard–Tao machinery on bounded gaps
between primes. They showed that for any m ≥ 1 there are infinitely many n
with d_n < d_{n+1} < ⋯ < d_{n+m}, and similarly for the decreasing case.
-/
theorem erdos_problem_6 :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2) :=
  sorry
