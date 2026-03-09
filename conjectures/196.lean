import Mathlib.GroupTheory.Perm.Basic

open Equiv

/--
Erdős Problem #196 [ErGr79, ErGr80]:

Must every permutation of ℕ contain a monotone 4-term arithmetic progression?
In other words, given a permutation x of ℕ must there be indices i < j < k < l
such that x(i), x(j), x(k), x(l) form an arithmetic progression?

Davis, Entringer, Graham, and Simmons [DEGS77] showed that every permutation
must contain a monotone 3-term AP and need not contain a monotone 5-term AP.
-/
theorem erdos_problem_196 (σ : Perm ℕ) :
    ∃ i j k l : ℕ, i < j ∧ j < k ∧ k < l ∧
      (σ j : ℤ) - (σ i : ℤ) = (σ k : ℤ) - (σ j : ℤ) ∧
      (σ k : ℤ) - (σ j : ℤ) = (σ l : ℤ) - (σ k : ℤ) :=
  sorry
