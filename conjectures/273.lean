import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic

/--
A **covering system** is a finite collection of congruence classes
(aᵢ, nᵢ) with each nᵢ ≥ 2, such that every integer belongs to at least
one class aᵢ (mod nᵢ).
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  (∀ p ∈ S, 2 ≤ p.2) ∧
    ∀ x : ℤ, ∃ p ∈ S, x ≡ p.1 [ZMOD (p.2 : ℤ)]

/--
Erdős Problem #273 [ErGr80, p.24]:

Is there a covering system all of whose moduli are of the form p − 1
for some primes p ≥ 5?

Selfridge found an example using divisors of 360 if p = 3 is allowed.
-/
theorem erdos_problem_273 :
    ∃ S : Finset (ℤ × ℕ),
      IsCoveringSystem S ∧
        ∀ p ∈ S, ∃ q : ℕ, Nat.Prime q ∧ 5 ≤ q ∧ p.2 = q - 1 :=
  sorry
