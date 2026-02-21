import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #473

Is there a permutation a₁, a₂, … of the positive integers such that
aₖ + aₖ₊₁ is always prime?

Asked by Segal. The answer is yes, as shown by Odlyzko.
-/

/--
Erdős Problem #473 (Segal):
There exists a permutation a₁, a₂, ... of the positive integers such that
aₖ + aₖ₊₁ is prime for all k. The answer is yes, as shown by Odlyzko.

The function `a : ℕ → ℕ` represents the sequence (0-indexed), and the three
conditions (injective, values positive, surjective onto positives) together
encode that `a` is a bijection from ℕ onto the positive integers.
-/
theorem erdos_problem_473 :
    ∃ a : ℕ → ℕ, Function.Injective a ∧
    (∀ n, 0 < a n) ∧
    (∀ m, 0 < m → ∃ n, a n = m) ∧
    ∀ k, Nat.Prime (a k + a (k + 1)) :=
  sorry
