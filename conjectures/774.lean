import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic

open Finset BigOperators

/-!
# Erdős Problem #774

A set A ⊆ ℕ is called *dissociated* if ∑_{n ∈ X} n ≠ ∑_{m ∈ Y} m for all
finite X, Y ⊆ A with X ≠ Y (i.e., all finite subset sums are distinct).

An infinite set A ⊆ ℕ is called *proportionately dissociated* if every finite
B ⊆ A contains a dissociated subset of size ≫ |B|; i.e., there exists c > 0
such that every finite B ⊆ A has a dissociated subset of size ≥ c · |B|.

Conjecture (Alon–Erdős [AlEr85]): Is every proportionately dissociated set
the union of finitely many dissociated sets?

Tags: number theory
-/

/-- A set A ⊆ ℕ is dissociated if all finite subset sums are distinct:
    for any two distinct finite subsets X ≠ Y of A, ∑ X ≠ ∑ Y. -/
def Dissociated774 (A : Set ℕ) : Prop :=
  ∀ X Y : Finset ℕ, ↑X ⊆ A → ↑Y ⊆ A → X ≠ Y → X.sum id ≠ Y.sum id

/-- A set A ⊆ ℕ is proportionately dissociated if there exists c > 0 such that
    every finite subset B ⊆ A contains a dissociated subset of size ≥ c · |B|. -/
def ProportionatelyDissociated774 (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ B : Finset ℕ, ↑B ⊆ A →
    ∃ D : Finset ℕ, D ⊆ B ∧ Dissociated774 ↑D ∧ (D.card : ℝ) ≥ c * B.card

/--
**Erdős Problem #774** (Alon–Erdős, 1985):
Is every proportionately dissociated set the union of finitely many
dissociated sets?
-/
theorem erdos_problem_774 :
    ∀ A : Set ℕ, A.Infinite →
    ProportionatelyDissociated774 A →
    ∃ n : ℕ, ∃ D : Fin n → Set ℕ,
      (∀ i, Dissociated774 (D i)) ∧ A ⊆ ⋃ i, D i :=
  sorry
