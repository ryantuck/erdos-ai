import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Erdős Problem #881

Let A ⊂ ℕ be an additive basis of order k which is minimal, in the sense that
if B ⊂ A is any infinite set then A \ B is not a basis of order k.

Must there exist an infinite B ⊂ A such that A \ B is a basis of order k + 1?

A problem from [Er98].
-/

/-- A set A ⊆ ℕ is an additive basis of order k if every sufficiently large
    natural number can be written as a sum of at most k elements from A
    (with repetition allowed). -/
def IsAdditiveBasis881 (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (l : List ℕ), l.length ≤ k ∧ (∀ x ∈ l, x ∈ A) ∧ l.sum = n

/-- A set A ⊆ ℕ is a minimal additive basis of order k if it is a basis of
    order k and removing any infinite subset destroys the basis property. -/
def IsMinimalAdditiveBasis881 (A : Set ℕ) (k : ℕ) : Prop :=
  IsAdditiveBasis881 A k ∧
  ∀ B : Set ℕ, B ⊆ A → Set.Infinite B → ¬IsAdditiveBasis881 (A \ B) k

/--
Erdős Problem #881 [Er98]:

If A ⊂ ℕ is a minimal additive basis of order k, must there exist an infinite
B ⊂ A such that A \ B is a basis of order k + 1?
-/
theorem erdos_problem_881 (A : Set ℕ) (k : ℕ)
    (hA : IsMinimalAdditiveBasis881 A k) :
    ∃ B : Set ℕ, B ⊆ A ∧ Set.Infinite B ∧ IsAdditiveBasis881 (A \ B) (k + 1) :=
  sorry
