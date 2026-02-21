import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Finite.Basic

open Real

noncomputable section

/-- The largest prime factor of a natural number n. Returns 0 if n ≤ 1. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.factorization.support.sup id

/-- F(n) = the largest prime factor of n(n+1). -/
def F368 (n : ℕ) : ℕ := largestPrimeFactor (n * (n + 1))

/-!
# Erdős Problem #368

How large is the largest prime factor of n(n+1)?

Let F(n) be the largest prime factor of n(n+1).

Known results:
- Pólya [Po18] proved F(n) → ∞ as n → ∞
- Mahler [Ma35] showed F(n) ≫ log log n
- Schinzel [Sc67b] observed F(n) ≤ n^{O(1/log log log n)} for infinitely many n
- Pasten [Pa24b] proved F(n) ≫ (log log n)² / log log log n

The conjectured truth is:
- Lower bound: F(n) ≫ (log n)² for all n
- Upper bound (Erdős [Er76d]): for every ε > 0, infinitely many n have F(n) < (log n)^{2+ε}
-/

/--
Erdős Problem #368 — Lower bound conjecture [Er65b, Er76d, ErGr80]:

The largest prime factor F(n) of n(n+1) satisfies F(n) ≫ (log n)² for all n.
That is, there exists c > 0 such that F(n) ≥ c · (log n)² for all sufficiently large n.
-/
theorem erdos_problem_368_lower :
    ∃ c : ℝ, 0 < c ∧
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (F368 n : ℝ) ≥ c * (Real.log n) ^ 2 :=
  sorry

/--
Erdős Problem #368 — Upper bound conjecture [Er76d]:

For every ε > 0, there are infinitely many n such that F(n) < (log n)^{2+ε}.
-/
theorem erdos_problem_368_upper :
    ∀ ε : ℝ, 0 < ε →
    Set.Infinite {n : ℕ | (F368 n : ℝ) < (Real.log n) ^ ((2 : ℝ) + ε)} :=
  sorry

end
