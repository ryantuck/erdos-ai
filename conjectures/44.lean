import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

/-- A finite set of natural numbers is a Sidon set (also called a B₂ set) if all
    pairwise sums a + b (allowing a = b) are distinct: whenever a + b = c + d
    with a, b, c, d ∈ A, we have {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
Erdős Problem #44 [Er84b, Er91, Er95, Er97c]:

Let N ≥ 1 and A ⊆ {1, ..., N} be a Sidon set. Is it true that, for any ε > 0,
there exist M and B ⊆ {N+1, ..., M} (which may depend on N, A, ε) such that
A ∪ B ⊆ {1, ..., M} is a Sidon set of size at least (1 - ε) · M^{1/2}?

In other words, can any Sidon set be extended to a nearly optimal-size Sidon set
in some larger interval?

See also [329] and [707].
-/
theorem erdos_problem_44 :
    ∀ (ε : ℝ), 0 < ε →
      ∀ (N : ℕ) (A : Finset ℕ),
        1 ≤ N →
        IsSidonSet A →
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        ∃ (M : ℕ) (B : Finset ℕ),
          N < M ∧
          (∀ b ∈ B, N + 1 ≤ b ∧ b ≤ M) ∧
          Disjoint A B ∧
          IsSidonSet (A ∪ B) ∧
          (((A ∪ B).card : ℝ) ≥ (1 - ε) * Real.sqrt (M : ℝ)) :=
  sorry
