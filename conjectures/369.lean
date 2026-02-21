import Mathlib.Data.Nat.Factors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Erdős Problem #369

Let ε > 0 and k ≥ 2. Is it true that, for all sufficiently large n, there is a
sequence of k consecutive integers in {1,…,n} all of which are n^ε-smooth?

The problem as literally stated is trivially true (take {1,…,k} with n > k^{1/ε}).
There are two non-trivial variants. The one formalized here requires the k consecutive
integers to lie in [n/2, n]. A positive answer follows from Balog–Wooley [BaWo98] for
infinitely many n, but the case of all sufficiently large n remains open.

See also [370] and [928].
-/

/-- A natural number `m` is `y`-smooth if every prime factor of `m` is at most `y`. -/
def IsSmooth (y : ℝ) (m : ℕ) : Prop :=
  ∀ p ∈ m.primeFactorsList, (p : ℝ) ≤ y

/--
Erdős Problem #369 [ErGr80, p.69]:

For all ε > 0 and k ≥ 2, for all sufficiently large n, there exist k consecutive
integers in [n/2, n] that are all n^ε-smooth.
-/
theorem erdos_problem_369
    (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ a : ℕ, n / 2 ≤ a ∧ a + k ≤ n + 1 ∧
        ∀ j : ℕ, j < k → IsSmooth ((n : ℝ) ^ ε) (a + j) :=
  sorry
