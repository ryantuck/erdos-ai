import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem #676

Is every sufficiently large integer of the form ap² + b for some prime p
and integer a ≥ 1 and 0 ≤ b < p?

The sieve of Eratosthenes implies that almost all integers are of this form,
and the Brun-Selberg sieve implies the number of exceptions in [1,x] is
≪ x/(log x)^c for some constant c > 0. Erdős believed it is 'rather unlikely'
that all large integers are of this form.
-/

/--
Erdős Problem #676 [Er79]:

Is every sufficiently large integer of the form ap² + b for some prime p
and integer a ≥ 1 and 0 ≤ b < p?

Formalized as: there exists N₀ such that for all n ≥ N₀, there exist a prime p,
a positive integer a, and a non-negative integer b < p with n = a * p² + b.
-/
theorem erdos_problem_676 :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ p a b : ℕ, Nat.Prime p ∧ a ≥ 1 ∧ b < p ∧ n = a * p ^ 2 + b :=
  sorry
