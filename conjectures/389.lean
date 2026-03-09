import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset

/--
Erdős Problem #389 [ErGr80,p.75]:

Is it true that for every n ≥ 1 there is a k such that
  n(n+1)⋯(n+k-1) ∣ (n+k)(n+k+1)⋯(n+2k-1)?

Asked by Erdős and Straus. For example when n = 2 we have k = 5:
  2 × 3 × 4 × 5 × 6 ∣ 7 × 8 × 9 × 10 × 11,
and when n = 3 we have k = 4:
  3 × 4 × 5 × 6 ∣ 7 × 8 × 9 × 10.
-/
theorem erdos_problem_389 :
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, 1 ≤ k ∧
        (∏ i ∈ range k, (n + i)) ∣ (∏ i ∈ range k, (n + k + i)) :=
  sorry
