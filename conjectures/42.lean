import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Finset

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Two sets A, B have disjoint difference sets (intersecting only at 0):
    (A - A) ∩ (B - B) = {0}. Equivalently, if a₁ - a₂ = b₁ - b₂ for
    a₁, a₂ ∈ A and b₁, b₂ ∈ B, then a₁ = a₂ and b₁ = b₂. -/
def DisjointDifferences (A B : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B,
    (a₁ : ℤ) - (a₂ : ℤ) = (b₁ : ℤ) - (b₂ : ℤ) → a₁ = a₂ ∧ b₁ = b₂

/--
Erdős Problem #42 [Er95]:

Let M ≥ 1 and N be sufficiently large in terms of M. Is it true that for every
Sidon set A ⊆ {1, ..., N} there is another Sidon set B ⊆ {1, ..., N} of size M
such that (A - A) ∩ (B - B) = {0}?

The statement is: for every M ≥ 1 there exists N₀ such that for all N ≥ N₀ and
every Sidon set A ⊆ {1, ..., N}, there exists a Sidon set B ⊆ {1, ..., N} with
|B| = M and (A - A) ∩ (B - B) = {0}.
-/
theorem erdos_problem_42 :
    ∀ (M : ℕ), 1 ≤ M →
      ∃ N₀ : ℕ, ∀ (N : ℕ), N₀ ≤ N →
        ∀ (A : Finset ℕ),
          IsSidonSet A →
          (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
          ∃ (B : Finset ℕ),
            IsSidonSet B ∧
            (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) ∧
            B.card = M ∧
            DisjointDifferences A B :=
  sorry
