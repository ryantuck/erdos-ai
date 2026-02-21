import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

/--
An additive arithmetic function: f(ab) = f(a) + f(b) whenever gcd(a,b) = 1.
-/
def IsAdditiveArithmeticFunction (f : ℕ → ℝ) : Prop :=
  ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b

/--
Erdős Problem #491 (proved by Wirsing [Wi70]):

Let f : ℕ → ℝ be an additive function (i.e. f(ab) = f(a) + f(b) whenever
gcd(a,b) = 1). If there is a constant c such that |f(n+1) - f(n)| < c for
all n, then there exist constants c' and M such that |f(n) - c' log n| ≤ M
for all n ≥ 1.
-/
theorem erdos_problem_491 (f : ℕ → ℝ)
    (hf : IsAdditiveArithmeticFunction f)
    (hbdd : ∃ c : ℝ, ∀ n : ℕ, |f (n + 1) - f n| < c) :
    ∃ c' : ℝ, ∃ M : ℝ, ∀ n : ℕ, 1 ≤ n →
      |f n - c' * Real.log (n : ℝ)| ≤ M := by
  sorry
