import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Real Finset BigOperators

noncomputable section

/--
The prime gap at index n: d(n) = p_{n+1} - p_n, where p_k is the k-th prime.
-/
def primeGap' (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/--
Erdős Problem #233 [Er40, Er55c, Er65b]:

Let d_n = p_{n+1} - p_n, where p_n is the n-th prime. Prove that
  ∑_{1 ≤ n ≤ N} d_n² ≪ N (log N)².

That is, there exists a constant C > 0 such that for all sufficiently large N,
  ∑_{n=0}^{N-1} d_n² ≤ C · N · (log N)².

Cramér proved O(N (log N)⁴) conditionally on the Riemann Hypothesis.
The prime number theorem gives the matching lower bound Ω(N (log N)²).
-/
theorem erdos_problem_233 :
    ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
        (∑ n ∈ range N, ((primeGap' n : ℝ) ^ 2)) ≤
          C * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 :=
  sorry

end
