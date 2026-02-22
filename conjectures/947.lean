import Mathlib.Data.Int.Basic

/--
Erdős Problem #947: There is no exact covering system with distinct moduli.
That is, there is no finite collection of congruence classes a_i (mod n_i) with
distinct moduli n_i ≥ 2 such that every integer belongs to exactly one of
these congruence classes.

This was proved independently by Mirsky-Newman and Davenport-Rado.
-/
theorem erdos_problem_947 :
    ¬ ∃ (k : ℕ) (a : Fin k → ℤ) (n : Fin k → ℕ),
      (∀ i, 2 ≤ n i) ∧
      (Function.Injective n) ∧
      (∀ x : ℤ, ∃! i : Fin k, (↑(n i) : ℤ) ∣ (x - a i)) :=
  sorry
