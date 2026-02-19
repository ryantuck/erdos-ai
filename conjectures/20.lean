import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

/--
A sunflower is a collection of sets S such that every pair of distinct sets in S
has the same intersection (the "kernel").
-/
def IsSunflower {α : Type*} [DecidableEq α] (S : Finset (Finset α)) : Prop :=
  ∃ K : Finset α, ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = K

/--
Erdős's Sunflower Conjecture (Problem #20):
There exists a constant c_k (depending only on k) such that any n-uniform family
of size at least c_k^n contains a sunflower of size k.
-/
theorem erdos_problem_20_conjecture :
  ∀ (k : ℕ), k > 2 → ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ,
    ∀ {α : Type} [DecidableEq α] (F : Finset (Finset α)),
      (∀ A ∈ F, A.card = n) →
      (F.card : ℝ) ≥ c ^ n →
      ∃ S ⊆ F, S.card = k ∧ IsSunflower S :=
sorry
