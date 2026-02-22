import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

/-!
# Erdős Problem #950

Let f(n) = Σ_{p<n} 1/(n-p), where the sum is over primes p < n.

Is it true that lim inf f(n) = 1 and lim sup f(n) = ∞?
Is it true that f(n) = o(log log n)?

This function was considered by de Bruijn, Erdős, and Turán, who showed that
  Σ_{n<x} f(n) ~ Σ_{n<x} f(n)² ~ x.

Reference: [Er77c]
https://www.erdosproblems.com/950

Tags: number theory, primes
-/

/-- The function f(n) = Σ_{p<n} 1/(n-p), summing over primes p less than n. -/
noncomputable def erdos950_f (n : ℕ) : ℝ :=
  ((Finset.range n).filter Nat.Prime).sum (fun p => 1 / ((n : ℝ) - (p : ℝ)))

/--
**Erdős Problem #950** — Part 1 [Er77c]:

lim inf_{n → ∞} f(n) = 1.

Equivalently: for every ε > 0,
  (a) f(n) > 1 - ε for all sufficiently large n, and
  (b) f(n) < 1 + ε for infinitely many n.
-/
theorem erdos_problem_950_liminf :
    ∀ ε : ℝ, ε > 0 →
    (∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → erdos950_f n > 1 - ε) ∧
    (∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ erdos950_f n < 1 + ε) :=
  sorry

/--
**Erdős Problem #950** — Part 2 [Er77c]:

lim sup_{n → ∞} f(n) = ∞.

Equivalently: for every M, there exist arbitrarily large n with f(n) > M.
-/
theorem erdos_problem_950_limsup :
    ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, n ≥ N₀ ∧ erdos950_f n > M :=
  sorry

/--
**Erdős Problem #950** — Part 3 [Er77c]:

f(n) = o(log log n), i.e., f(n) / log(log n) → 0 as n → ∞.
-/
theorem erdos_problem_950_little_o :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      erdos950_f n < ε * Real.log (Real.log (n : ℝ)) :=
  sorry

end
