import Mathlib.Data.Nat.Factors
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

open Set

/-!
# Erdős Problem #413

Let ω(n) count the number of distinct primes dividing n. A natural number n
is called a "barrier" for ω if m + ω(m) ≤ n for all m < n.

Part 1: Are there infinitely many barriers for ω?

Part 2: Does there exist an ε > 0 such that there are infinitely many n
where m + ε * ω(m) ≤ n for all m < n?

Reference: [Er79, Er79d, ErGr80, Er92e, Er95c]
https://www.erdosproblems.com/413
-/

/-- The number of distinct prime factors of n. -/
noncomputable def omega (n : ℕ) : ℕ :=
  (Nat.primeFactorsList n).toFinset.card

/-- n is a barrier for ω: for all m < n, m + ω(m) ≤ n. -/
def IsBarrier (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → m + omega m ≤ n

/--
Erdős Problem #413, Part 1 [Er79, Er79d, ErGr80]:

There are infinitely many barriers for ω, i.e., infinitely many n such that
m + ω(m) ≤ n for all m < n.
-/
theorem erdos_problem_413_part1 :
    Set.Infinite {n : ℕ | IsBarrier n} :=
  sorry

/--
Erdős Problem #413, Part 2 [Er79, ErGr80]:

There exists an ε > 0 such that there are infinitely many n where
m + ε * ω(m) ≤ n for all m < n.
-/
theorem erdos_problem_413_part2 :
    ∃ ε : ℝ, ε > 0 ∧
    Set.Infinite {n : ℕ |
      ∀ m : ℕ, m < n →
        (m : ℝ) + ε * (omega m : ℝ) ≤ (n : ℝ)} :=
  sorry
