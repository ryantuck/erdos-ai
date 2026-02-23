import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic

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
Erdős Problem #43 [Er95]:

If A, B ⊆ {1, ..., N} are two Sidon sets such that (A - A) ∩ (B - B) = {0},
then is it true that
  C(|A|, 2) + C(|B|, 2) ≤ C(f(N), 2) + O(1),
where f(N) is the maximum possible size of a Sidon set in {1, ..., N}?

Here S represents a maximum-size Sidon set in {1, ..., N}, so S.card = f(N).
The O(1) term is captured by the absolute constant C.
-/
theorem erdos_problem_43 :
    ∃ C : ℕ, ∀ (N : ℕ) (A B S : Finset ℕ),
      IsSidonSet A → IsSidonSet B → IsSidonSet S →
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
      (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
      (∀ s ∈ S, 1 ≤ s ∧ s ≤ N) →
      (∀ T : Finset ℕ, IsSidonSet T → (∀ t ∈ T, 1 ≤ t ∧ t ≤ N) → T.card ≤ S.card) →
      DisjointDifferences A B →
      Nat.choose A.card 2 + Nat.choose B.card 2 ≤ Nat.choose S.card 2 + C :=
  sorry
