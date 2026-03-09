import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real

noncomputable section

/--
The prime gap at index n: d(n) = p_{n+1} - p_n, where p_k is the k-th prime.
-/
def primeGap (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/--
r(x) is the smallest positive even integer t such that d_n = t has no solution
for n ≤ x. Equivalently, the smallest positive even integer not appearing
among the prime gaps {d_1, d_2, …, d_x}.

Defined via sInf; the set is always nonempty since there are only finitely
many distinct prime gaps up to index x but infinitely many positive even integers.
-/
def smallestMissingEvenGap (x : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ 2 ∣ t ∧ ∀ n : ℕ, n ≤ x → primeGap n ≠ t}

/--
Erdős Problem #853 (weak form) [Er85c]:

Let d_n = p_{n+1} - p_n and let r(x) be the smallest even integer t such that
d_n = t has no solution for n ≤ x. Is it true that r(x) → ∞?
-/
theorem erdos_problem_853_weak :
    ∀ B : ℕ, ∃ X : ℕ, ∀ x : ℕ, x ≥ X → smallestMissingEvenGap x ≥ B :=
  sorry

/--
Erdős Problem #853 (strong form) [Er85c]:

Is it true that r(x) / log x → ∞?
-/
theorem erdos_problem_853_strong :
    ∀ C : ℝ, 0 < C →
      ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
        (smallestMissingEvenGap x : ℝ) > C * Real.log (x : ℝ) :=
  sorry

end
