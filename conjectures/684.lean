import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset BigOperators Classical

noncomputable section

/-!
# Erdős Problem #684

For 0 ≤ k ≤ n write C(n,k) = uv where the only primes dividing u are in [2,k]
and the only primes dividing v are in (k,n]. Let f(n) be the smallest k such
that u > n². Give bounds for f(n).

Mahler's theorem implies f(n) → ∞ as n → ∞, but is ineffective and gives
no explicit bounds. Tang proved f(n) ≤ n^{30/43 + o(1)}.
A heuristic suggests f(n) ∼ 2 log n for most n.
-/

/-- The k-smooth part of a natural number m: the product of p^{v_p(m)} over
    all primes p ≤ k. This is the largest divisor of m whose prime factors
    are all at most k. -/
noncomputable def smoothPart (m k : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, p ^ (m.factorization p)

/-- f(n) for Erdős Problem #684: the smallest k such that the k-smooth part
    of C(n,k) exceeds n². Returns 0 if no such k exists. -/
noncomputable def erdos684_f (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, smoothPart (n.choose k) k > n ^ 2
  then Nat.find h
  else 0

/--
Erdős Problem #684 [Er79d]: f(n) → ∞ as n → ∞.

For every bound K, for all sufficiently large n, the smallest k such that the
k-smooth part of C(n,k) exceeds n² is greater than K.

This follows from Mahler's theorem. The problem asks for effective bounds
on the growth of f(n).
-/
theorem erdos_problem_684 :
    ∀ K : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → erdos684_f n > K :=
  sorry

/--
Erdős Problem #684, upper bound (Tang):

f(n) ≤ n^{30/43 + o(1)}. For every ε > 0, for all sufficiently large n,
f(n) ≤ n^{30/43 + ε}.
-/
theorem erdos_problem_684_upper :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos684_f n : ℝ) ≤ (n : ℝ) ^ ((30 : ℝ) / 43 + ε) :=
  sorry

end
