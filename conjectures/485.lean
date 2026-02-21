import Mathlib.Algebra.Polynomial.Basic

open Polynomial

/--
Erdős Problem #485 (Erdős–Rényi conjecture, proved by Schinzel [Sc87]):

Let f(k) be the minimum number of nonzero terms in P(x)², where P ∈ ℚ[x]
ranges over all polynomials with exactly k nonzero terms. Is it true that
f(k) → ∞ as k → ∞?

Schinzel proved f(k) > log(log k) / log 2. Schinzel and Zannier [ScZa09]
improved this to f(k) ≫ log k.
-/
theorem erdos_problem_485 :
    ∀ M : ℕ, ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
    ∀ P : ℚ[X], P.support.card = k →
    M ≤ (P ^ 2).support.card :=
  sorry
