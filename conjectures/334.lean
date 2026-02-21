import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean

open Classical

/-- A natural number is B-smooth if all its prime factors are at most B. -/
def IsSmooth (B n : ℕ) : Prop := ∀ p ∈ n.primeFactorsList, p ≤ B

/--
Erdős Problem #334 [ErGr80, p.70] [Er82d, p.55]:

Find the best function f(n) such that every n can be written as n = a + b
where both a, b are f(n)-smooth (not divisible by any prime p > f(n)).

Erdős originally asked if f(n) ≤ n^{1/3}. Balog [Ba89] proved
f(n) ≪_ε n^{4/(9√e) + ε} for all ε > 0. It is conjectured that
f(n) ≤ n^{o(1)}, or even f(n) ≤ e^{O(√(log n))}.

We formalize the conjecture that f(n) = n^{o(1)}: for every ε > 0,
for sufficiently large n, n can be written as a sum of two ⌊n^ε⌋-smooth
numbers.
-/
theorem erdos_problem_334 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a b : ℕ, a + b = n ∧
          IsSmooth (⌊(n : ℝ) ^ ε⌋₊) a ∧
          IsSmooth (⌊(n : ℝ) ^ ε⌋₊) b :=
  sorry
