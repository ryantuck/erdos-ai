import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Erdős Problem #729

Let C > 0 be a constant. Are there infinitely many integers a, b, n with
a + b > n + C log n such that the denominator of n!/(a!b!) contains only
primes ≪_C 1?

Erdős proved that if a!b! ∣ n! then a + b ≤ n + O(log n). This problem asks
whether the same bound holds when divisibility is only required "up to small
primes," i.e., the denominator of n!/(a!b!) is supported only on bounded primes.

The answer is yes (the bound still holds): for any C > 0 and any prime bound P,
there are only finitely many triples (a, b, n) with a + b > n + C log n such that
all prime factors of the denominator of n!/(a!b!) are at most P.

Proved by Barreto and Leeham.
-/

/-- The denominator of n!/(a!·b!), when written in lowest terms, is P-smooth:
    all its prime factors are at most P. -/
def denomPSmooth729 (a b n P : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p →
    p ∣ ((n.factorial : ℚ) / ((a.factorial : ℚ) * (b.factorial : ℚ))).den → p ≤ P

/--
Erdős Problem #729 [EGRS75]:

For any C > 0 and any prime bound P, the set of triples (a, b, n) such that
a + b > n + C · log n and the denominator of n!/(a!b!) is P-smooth, is finite.
-/
theorem erdos_problem_729 (C : ℝ) (hC : C > 0) (P : ℕ) :
    Set.Finite {t : ℕ × ℕ × ℕ |
      (t.1 : ℝ) + (t.2.1 : ℝ) > (t.2.2 : ℝ) + C * Real.log (t.2.2 : ℝ) ∧
      denomPSmooth729 t.1 t.2.1 t.2.2 P} :=
  sorry
