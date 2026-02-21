import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

/--
Erdős Problem #205 (Disproved) [ErGr80, p.28]:

Erdős and Graham asked whether all sufficiently large n can be written as
2^k + m for some k ≥ 0, where Ω(m) < log(log(m)). Here Ω(m) is the number
of prime divisors of m counted with multiplicity, given by `(Nat.factors m).length`.

This was disproved by Barreto and Leeham. The result was quantified by Tao
and Alexeev: there are infinitely many n such that for all k with 2^k ≤ n,
n - 2^k has at least ≫ (log n / log log n)^{1/2} prime factors.

We formalize the negation of the original conjecture, which is the true statement.
-/
theorem erdos_problem_205 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) :=
  sorry
