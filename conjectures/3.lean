import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
The set A ⊆ ℕ has divergent reciprocal sum, i.e., ∑_{n ∈ A} 1/n = ∞.
Expressed as: for every bound M, some finite subset of A has reciprocal sum ≥ M.
-/
def DivergentReciprocalSum (A : Set ℕ) : Prop :=
  ∀ M : ℝ, ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧
    M ≤ ∑ n ∈ F, (1 : ℝ) / (n : ℝ)

/--
The set A contains an arithmetic progression of length k:
there exist a, d ∈ ℕ with d ≥ 1 such that {a, a+d, a+2d, …, a+(k-1)d} ⊆ A.
-/
def ContainsArithProg (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/--
Erdős Problem #3 [Er74b, Er75b, Er77c, ErGr79, Er80, Er81, Er83c]:

If A ⊆ ℕ has ∑_{n ∈ A} 1/n = ∞ then A must contain arbitrarily long
arithmetic progressions.

This is the Erdős conjecture on arithmetic progressions, one of his most
famous open problems, with a $5000 prize. The case k = 3 was proved by
Bloom and Sisask (2020).
-/
theorem erdos_problem_3
    (A : Set ℕ)
    (hA : DivergentReciprocalSum A) :
    ∀ k : ℕ, ContainsArithProg A k :=
  sorry
