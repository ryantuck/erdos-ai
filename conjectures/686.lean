import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

open Finset

/--
The product of k consecutive integers starting from n+1, i.e., (n+1)(n+2)⋯(n+k).
-/
def prodConsecutive (n k : ℕ) : ℕ :=
  (Finset.Icc (n + 1) (n + k)).prod id

/--
Erdős Problem #686 [Er79d]:

Can every integer N ≥ 2 be written as
  N = ∏_{1≤i≤k}(m+i) / ∏_{1≤i≤k}(n+i)
for some k ≥ 2 and m ≥ n+k?
-/
theorem erdos_problem_686 :
    ∀ N : ℕ, 2 ≤ N →
      ∃ k : ℕ, 2 ≤ k ∧
        ∃ m n : ℕ, m ≥ n + k ∧
          N * prodConsecutive n k = prodConsecutive m k :=
  sorry
