import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open BigOperators Finset

/--
A signing δ : A → {-1,1} of the reciprocals of A sums to zero:
∑_{n ∈ A} δ(n)/n = 0.
-/
def SignedReciprocalSumZero (A : Finset ℕ) (δ : ℕ → ℤ) : Prop :=
  (∀ a ∈ A, δ a = 1 ∨ δ a = -1) ∧
    ∑ n ∈ A, (δ n : ℝ) / (n : ℝ) = 0

/--
A signing δ of A is *minimal*: the signed reciprocal sum over A is zero,
but the signed reciprocal sum over every non-empty proper subset A' ⊊ A
is non-zero.
-/
def MinimalSignedReciprocalSumZero (A : Finset ℕ) (δ : ℕ → ℤ) : Prop :=
  SignedReciprocalSumZero A δ ∧
    ∀ A' : Finset ℕ, A' ⊆ A → A' ≠ ∅ → A' ≠ A →
      ∑ n ∈ A', (δ n : ℝ) / (n : ℝ) ≠ 0

/--
f(N) is the size of the largest A ⊆ {1,…,N} that admits a minimal
signed reciprocal sum of zero.
-/
def MaxMinimalSignedReciprocalSet (N : ℕ) (k : ℕ) : Prop :=
  (∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ A.card = k ∧
    ∃ δ : ℕ → ℤ, MinimalSignedReciprocalSumZero A δ) ∧
  (∀ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
    (∃ δ : ℕ → ℤ, MinimalSignedReciprocalSumZero A δ) → A.card ≤ k)

/--
Erdős Problem #319 [ErGr80]:

What is the size of the largest A ⊆ {1,…,N} such that there is a
function δ : A → {-1,1} with ∑_{n ∈ A} δ(n)/n = 0, yet
∑_{n ∈ A'} δ(n)/n ≠ 0 for every non-empty proper subset A' ⊊ A?

A lower bound of |A| ≥ (1 − 1/e + o(1))N follows from work of
Croot (2001), as observed by Adenwalla.

The conjecture here is that this maximum is asymptotic to cN for
some constant c (in particular it grows linearly in N).
-/
theorem erdos_problem_319 :
    ∃ c : ℝ, 0 < c ∧
      ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ k : ℕ,
        MaxMinimalSignedReciprocalSet N k →
        |((k : ℝ) / (N : ℝ)) - c| < ε :=
  sorry
