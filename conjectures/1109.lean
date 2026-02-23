import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Pointwise Real

/--
Erdős Problem #1109:
Let f(N) be the size of the largest subset A ⊆ {1, ..., N} such that every
n ∈ A + A is squarefree. Is it true that f(N) ≤ (log N)^{O(1)}?

Formalized as: there exist constants C > 0 and k > 0 such that for all
sufficiently large N, every subset A ⊆ {1, ..., N} whose sumset A + A is
entirely squarefree satisfies |A| ≤ C · (log N)^k.

First studied by Erdős and Sárközy [ErSa87], who proved
  log N ≪ f(N) ≪ N^{3/4} · log N.
Konyagin [Ko04] improved this to
  (log log N) · (log N)² ≪ f(N) ≪ N^{11/15 + o(1)}.
-/
theorem erdos_problem_1109_conjecture :
    ∃ C : ℝ, C > 0 ∧ ∃ k : ℕ, 0 < k ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ n ∈ A + A, Squarefree n) →
      (A.card : ℝ) ≤ C * (Real.log N) ^ k :=
  sorry
