import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/--
A finite system of congruences `{(aᵢ, mᵢ)}` is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence `n ≡ aᵢ (mod mᵢ)`.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
A covering system has **distinct moduli** if no two congruences share the same modulus.
-/
def HasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q

/--
Erdős Problem #7:

Is there a distinct covering system all of whose moduli are odd?

A **distinct covering system** is a finite collection of congruences
`{n ≡ aᵢ (mod mᵢ)}` where all moduli `mᵢ` are pairwise distinct,
covering every integer. The question asks whether such a system can
exist with all moduli odd.

Known results:
- Hough and Nielsen (2019) proved that in any distinct covering system,
  at least one modulus must be divisible by 2 or 3. A simpler proof
  was given by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba (2022),
  who also showed that the lcm of any odd covering system's moduli must
  be divisible by 9 or 15.
- Balister et al. (2022) proved no odd distinct covering system exists
  if the moduli are additionally required to be squarefree.
  The general odd case remains open.
-/
theorem erdos_problem_7 :
    ∃ S : Finset (ℤ × ℕ),
      IsCoveringSystem S ∧
      HasDistinctModuli S ∧
      ∀ p ∈ S, Odd p.2 :=
  sorry
