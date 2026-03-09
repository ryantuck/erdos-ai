import Mathlib.Data.Nat.Totient
import Mathlib.Data.Int.Lemmas

/-!
# Erdős Problem #828

Is it true that, for any $a \in \mathbb{Z}$, there are infinitely many $n$ such that
$\phi(n) \mid n + a$?

A conjecture of Graham. Lehmer has conjectured that φ(n) ∣ n − 1 if and only if n is
prime. It is an easy exercise to show that φ(n) ∣ n if and only if n = 2ᵃ3ᵇ.
-/

/--
Erdős Problem #828 [Er83]:

For any integer a, there are infinitely many positive integers n such that
φ(n) ∣ n + a.
-/
theorem erdos_problem_828 (a : ℤ) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ (Nat.totient n : ℤ) ∣ (↑n + a) :=
  sorry
