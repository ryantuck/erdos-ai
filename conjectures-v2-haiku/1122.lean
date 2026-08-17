import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Interval.Finset.Nat

noncomputable section
open Classical Finset

namespace Erdos1122

def answer : Prop → Prop := id

/--
Erdős Problem #1122 [Er46]:

Let f : ℕ → ℝ be an additive function (i.e., f(ab) = f(a) + f(b) whenever
gcd(a,b) = 1). Let A = {n ≥ 1 : f(n+1) < f(n)}.
If |A ∩ [1,X]| = o(X) (the set A has natural density zero), then
f(n) = c·log(n) for some c ∈ ℝ?

Erdős proved that f(n) = c·log(n) if A is empty, or if f(n+1) - f(n) = o(1).
Partial progress was made by Mangerel [Ma22], who proved the conjecture holds if
|A ∩ [1,X]| ≪ X/(log X)^{2+c} for some c > 0, subject to conditions on g(p).

See also Erdős Problem 491 for the stronger hypothesis |f(n+1) − f(n)| < c.

[Er46] Erdős, P., "On the distribution function of additive functions",
       Ann. of Math. (2) 47 (1946), 1–20.
[Ma22] Mangerel, A. P., "On additive functions with small increments", 2022.
-/
theorem erdos_problem_1122
    (f : ℕ → ℝ)
    (hf_add : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a + f b)
    (hA : ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ X : ℕ, X ≥ N →
      (((Finset.Icc 1 X).filter (fun n => f (n + 1) < f n)).card : ℝ) ≤ ε * (X : ℝ)) :
    answer sorry ↔ (∃ c : ℝ, ∀ n : ℕ, 1 ≤ n → f n = c * Real.log (n : ℝ)) :=
  sorry

end Erdos1122
