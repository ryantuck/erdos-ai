import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
open Set Finset

/--
The sumset A + A = {a₁ + a₂ | a₁, a₂ ∈ A}.
-/
def sumset' (A : Set ℕ) : Set ℕ :=
  {n | ∃ a₁ ∈ A, ∃ a₂ ∈ A, n = a₁ + a₂}

/--
The upper density of A ⊆ ℕ is positive: there exists δ > 0 such that
|A ∩ {1, …, N}| ≥ δ · N for infinitely many N.
-/
def HasPositiveUpperDensity' (A : Set ℕ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ A ∧ (∀ x ∈ F, 1 ≤ x ∧ x ≤ N) ∧
        δ * (N : ℝ) ≤ (F.card : ℝ)

/--
A set S ⊆ ℕ has **bounded gaps** if there exists N such that every interval
[n, n + N] contains an element of S.
-/
def HasBoundedGaps' (S : Set ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, ∃ d ∈ S, n ≤ d ∧ d ≤ n + N

/--
A is an additive basis of order 2: every sufficiently large natural number
can be written as a sum of two elements of A.
-/
def IsBasisOrder2 (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → n ∈ sumset' A

/--
Erdős Problem #741 (Part 1) [Er94b]:

Let A ⊆ ℕ be such that A + A has positive density. Can one always decompose
A = A₁ ⊔ A₂ (a disjoint partition) such that A₁ + A₁ and A₂ + A₂ both have
positive density?

A problem of Burr and Erdős.
-/
theorem erdos_problem_741a
    (A : Set ℕ)
    (hA : HasPositiveUpperDensity' (sumset' A)) :
    ∃ A₁ A₂ : Set ℕ,
      A₁ ∪ A₂ = A ∧ Disjoint A₁ A₂ ∧
      HasPositiveUpperDensity' (sumset' A₁) ∧
      HasPositiveUpperDensity' (sumset' A₂) :=
  sorry

/--
Erdős Problem #741 (Part 2) [Er94b]:

Is there a basis A of order 2 such that for any partition A = A₁ ⊔ A₂,
A₁ + A₁ and A₂ + A₂ cannot both have bounded gaps?

Erdős thought he could construct such a basis but 'could never quite finish
the proof'.
-/
theorem erdos_problem_741b :
    ∃ A : Set ℕ, IsBasisOrder2 A ∧
      ∀ A₁ A₂ : Set ℕ,
        A₁ ∪ A₂ = A → Disjoint A₁ A₂ →
        ¬(HasBoundedGaps' (sumset' A₁) ∧ HasBoundedGaps' (sumset' A₂)) :=
  sorry
