import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

open Finset

open scoped Pointwise

/-- A finite set of integers is a **Sidon set** (or B₂ set) if all pairwise
    sums are distinct: whenever a + b = c + d with a, b, c, d ∈ A, we have
    {a, b} = {c, d} as multisets. -/
def IsSidonSet (A : Finset ℤ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/--
Erdős Problem #757 [Er97b]:

Let A ⊂ ℤ be a finite set of size n such that every 4-element subset B ⊆ A
has |B - B| ≥ 11 (where B - B = {b₁ - b₂ | b₁, b₂ ∈ B}). Then A must
contain a Sidon set of size ≥ cn for some absolute constant c > 1/2.

For a 4-element Sidon set, |B - B| = 13, so the hypothesis says every
4-element subset has at most one "missing" difference. Equivalently, every
four points determine at least five distinct distances.

Erdős and Sós proved c ≥ 1/2. Gyárfás and Lehel proved 1/2 < c < 3/5
(the upper bound witnessed by the first n Fibonacci numbers). The exact
value of the best constant is unknown.
-/
theorem erdos_problem_757 :
    ∃ c : ℝ, c > 1 / 2 ∧
      ∀ (A : Finset ℤ),
        (∀ B : Finset ℤ, B ⊆ A → B.card = 4 → (B - B).card ≥ 11) →
        ∃ S : Finset ℤ, S ⊆ A ∧ IsSidonSet S ∧ (S.card : ℝ) ≥ c * A.card :=
  sorry
