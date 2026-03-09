import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
The target `n` is NOT representable as a sum of any subset of `A`.
-/
def NotSubsetSum (A : Finset ℕ) (n : ℕ) : Prop :=
  ∀ S ∈ A.powerset, S.sum id ≠ n

/--
`A` is a valid candidate: `A ⊆ {1, …, ⌊cn⌋}` and `n` is not a subset sum of `A`.
-/
def IsSubsetSumFreeIn (c : ℝ) (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ (a : ℝ) ≤ c * n) ∧ NotSubsetSum A n

/--
Erdős Problem #361 [ErGr80, p.59]:

Let c > 0 and n be some large integer. What is the size of the largest
A ⊆ {1, …, ⌊cn⌋} such that n is not a sum of a subset of A? Does this
depend on n in an irregular way?

Part 1: For every c > 0 and every n, there is a maximum-size such set —
that is, among all valid A the cardinality is bounded and the maximum is
attained.
-/
theorem erdos_problem_361_max_exists (c : ℝ) (hc : 0 < c) (n : ℕ) :
    ∃ A : Finset ℕ, IsSubsetSumFreeIn c n A ∧
      ∀ B : Finset ℕ, IsSubsetSumFreeIn c n B → B.card ≤ A.card :=
  sorry

/--
Part 2 (the "irregular dependence" question): For every c > 0, the
maximum cardinality is not eventually monotone in n. That is, there exist
arbitrarily large n₁ < n₂ < n₃ where the maximum cardinality goes
down then up again.
-/
theorem erdos_problem_361_irregular (c : ℝ) (hc : 0 < c) :
    ∀ M : ℕ, ∃ n₁ n₂ n₃ : ℕ,
      M ≤ n₁ ∧ n₁ < n₂ ∧ n₂ < n₃ ∧
      ∃ A₁ A₂ A₃ : Finset ℕ,
        IsSubsetSumFreeIn c n₁ A₁ ∧
        IsSubsetSumFreeIn c n₂ A₂ ∧
        IsSubsetSumFreeIn c n₃ A₃ ∧
        (∀ B, IsSubsetSumFreeIn c n₁ B → B.card ≤ A₁.card) ∧
        (∀ B, IsSubsetSumFreeIn c n₂ B → B.card ≤ A₂.card) ∧
        (∀ B, IsSubsetSumFreeIn c n₃ B → B.card ≤ A₃.card) ∧
        A₁.card > A₂.card ∧
        A₂.card < A₃.card :=
  sorry
