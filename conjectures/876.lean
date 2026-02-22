import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Monotone.Basic

open Finset BigOperators

/--
A set A ⊆ ℕ is sum-free in the sense of Erdős if no element of A can be expressed
as the sum of finitely many distinct smaller elements of A.
-/
def IsSumFreeErdos (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty → (∀ x ∈ S, x ∈ A) → (∀ x ∈ S, x < a) → S.sum id ≠ a

/--
Erdős Problem #876: Let A = {a₁ < a₂ < ⋯} ⊆ ℕ be an infinite sum-free set (no element
is the sum of finitely many distinct smaller elements of A). Is it possible that
a_{n+1} - a_n < n for all sufficiently large n?

Erdős notes that Graham proved there exists such a sequence with a_{n+1} - a_n < n^{1+o(1)}.
-/
theorem erdos_problem_876_conjecture :
  ∃ a : ℕ → ℕ, StrictMono a ∧
    IsSumFreeErdos (Set.range a) ∧
    ∃ N, ∀ n ≥ N, a (n + 1) - a n < n + 1 :=
sorry
