import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

/--
An integer `m` has a prime factor greater than `k`.
-/
def HasPrimeFactorGt (m k : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p > k ∧ p ∣ m

/--
Every set of `n` consecutive integers greater than `k` contains one
with a prime factor greater than `k`.
-/
def ConsecutiveIntegerProperty (k n : ℕ) : Prop :=
  ∀ m : ℕ, m > k →
    ∃ i : ℕ, i < n ∧ HasPrimeFactorGt (m + i) k

/--
Erdős Problem #961 [Er76e]:

Let f(k) be the minimal n such that every set of n consecutive integers > k
contains an integer divisible by a prime > k. Estimate f(k).

In other words, how large can a consecutive set of k-smooth integers be?
Sylvester and Schur proved f(k) ≤ k and Erdős proved f(k) < 3k / log k.
Jutila, Ramachandra, and Shorey improved this to
f(k) ≪ (log log log k / log log k) · (k / log k).

It is conjectured that f(k) ≪ (log k)^C for some constant C, i.e., f(k) is
bounded by a fixed polynomial in log k.
-/
theorem erdos_problem_961 :
    ∃ C : ℝ, 0 < C ∧
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        ∃ n : ℕ, ConsecutiveIntegerProperty k n ∧
          (n : ℝ) ≤ (Real.log k) ^ C :=
  sorry
