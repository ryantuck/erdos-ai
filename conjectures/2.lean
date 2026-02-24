import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

/--
A finite system of congruences `{(aᵢ, mᵢ)}` is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence `n ≡ aᵢ (mod mᵢ)`.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
Erdős Problem #2:

Erdős asked whether the smallest modulus of a covering system can be arbitrarily
large (he expected the answer to be yes). Hough (2015), building on work of
Filaseta, Ford, Konyagin, Pomerance, and Yu (2007), showed the answer is **no**:
every covering system has smallest modulus at most 10¹⁶. Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba (2022) gave a simpler proof and improved the
bound to 616000. The best known lower bound is 42, due to Owens (2014).

Formally: there exists an absolute constant B such that every covering system
contains a congruence whose modulus is at most B.
-/
theorem erdos_problem_2 :
    ∃ B : ℕ, ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S →
      ∃ p ∈ S, p.2 ≤ B :=
  sorry
