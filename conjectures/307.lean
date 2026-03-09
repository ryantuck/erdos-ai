import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
Erdős Problem #307 [ErGr80]:

Are there two finite sets of primes P, Q such that
  (∑_{p ∈ P} 1/p) · (∑_{q ∈ Q} 1/q) = 1?

Asked by Barbeau [Ba76]. It is easy to see that P and Q must be disjoint,
and ∑_{p ∈ P∪Q} 1/p ≥ 2, whence |P ∪ Q| ≥ 60.
-/
theorem erdos_problem_307 :
    ∃ (P Q : Finset ℕ),
      (∀ p ∈ P, Nat.Prime p) ∧
      (∀ q ∈ Q, Nat.Prime q) ∧
      (∑ p ∈ P, (1 : ℚ) / (p : ℚ)) *
      (∑ q ∈ Q, (1 : ℚ) / (q : ℚ)) = 1 :=
  sorry
