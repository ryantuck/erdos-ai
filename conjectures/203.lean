import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

/--
Erdős Problem #203 [ErGr80,p.27]:

Is there an integer m ≥ 1 with gcd(m, 6) = 1 such that none of
2^k · 3^ℓ · m + 1 are prime, for any k, ℓ ≥ 0?

This is a generalization of Sierpiński numbers (where only powers of 2 are
considered) to products of powers of 2 and 3.
-/
theorem erdos_problem_203 :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.Coprime m 6 ∧
      ∀ k ℓ : ℕ, ¬ Nat.Prime (2 ^ k * 3 ^ ℓ * m + 1) :=
  sorry
