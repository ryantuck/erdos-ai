import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #964

Let τ(n) count the number of divisors of n. Is the sequence
τ(n+1)/τ(n) everywhere dense in (0,∞)?

This has been proved unconditionally by Eberhard [Eb25], who in fact showed
that every positive rational can be written as such a ratio.
-/

/--
Erdős Problem #964 [Er86b]:

The set {τ(n+1)/τ(n) : n ≥ 1} is dense in (0, ∞).

For every positive real r and every ε > 0, there exists a natural number n ≥ 1
such that |τ(n+1)/τ(n) - r| < ε.
-/
theorem erdos_problem_964 :
    ∀ r : ℝ, r > 0 → ∀ ε : ℝ, ε > 0 →
    ∃ n : ℕ, n ≥ 1 ∧
      |((Nat.divisors (n + 1)).card : ℝ) / ((Nat.divisors n).card : ℝ) - r| < ε :=
  sorry
