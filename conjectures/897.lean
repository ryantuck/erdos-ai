import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

namespace Erdos897

/-!
# Erdős Problem #897 (DISPROVED)

A conjecture of Erdős and Wirsing [Er72].

Let f : ℕ → ℝ be an additive function (f(ab) = f(a) + f(b) when gcd(a,b) = 1)
such that lim sup_{p,k} f(p^k) / log(p^k) = ∞.

Erdős asked: is it true that lim sup_n (f(n+1) - f(n)) / log n = ∞?
Or perhaps even lim sup_n f(n+1) / f(n) = ∞?

Both questions were answered in the negative. A simple counterexample is to take
f(q) = g(q) log q for all prime powers q, where g is sufficiently slowly growing.
This construction appears in Wirsing [Wi81], credited to Erdős.

We formalize the negation: there exists an additive function f with
lim sup f(p^k) / log(p^k) = ∞, yet lim sup (f(n+1) - f(n)) / log n is finite
(and in fact can be made 0).
-/

/-- A function f : ℕ → ℝ is additive if f(ab) = f(a) + f(b) whenever gcd(a,b) = 1,
    and f(1) = 0. -/
def IsAdditiveArithFun (f : ℕ → ℝ) : Prop :=
  f 1 = 0 ∧ ∀ a b : ℕ, 0 < a → 0 < b → Nat.Coprime a b → f (a * b) = f a + f b

/-- The lim sup of f(p^k) / log(p^k) over all prime powers p^k is infinite:
    for every bound M, there exist p prime and k ≥ 1 with f(p^k) / log(p^k) > M. -/
def PrimePowerLimSupInfinite (f : ℕ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ p k : ℕ, Nat.Prime p ∧ 1 ≤ k ∧
    M < f (p ^ k) / Real.log (p ^ k : ℝ)

/-- The lim sup of (f(n+1) - f(n)) / log n is at most C:
    there exists N₀ such that for all n ≥ N₀, (f(n+1) - f(n)) / log n ≤ C. -/
def ConsecDiffBounded (f : ℕ → ℝ) (C : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    (f (n + 1) - f n) / Real.log (n : ℝ) ≤ C

/--
Erdős Problem #897 (Disproved, Wirsing [Wi81] / Erdős):

There exists an additive function f with lim sup f(p^k)/log(p^k) = ∞
such that (f(n+1) - f(n)) / log n is eventually bounded (disproving
the conjecture that the lim sup must be ∞).
-/
theorem erdos_problem_897 :
    ∃ f : ℕ → ℝ,
      IsAdditiveArithFun f ∧
      PrimePowerLimSupInfinite f ∧
      ∃ C : ℝ, ConsecDiffBounded f C :=
  sorry

end Erdos897
