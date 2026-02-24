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
All moduli in a covering system are **monochromatic** under a colouring `χ : ℕ → Fin k`
if there exists a colour `c` such that every modulus in `S` receives colour `c`.
-/
def HasMonochromaticModuli {k : ℕ} (χ : ℕ → Fin k) (S : Finset (ℤ × ℕ)) : Prop :=
  ∃ c : Fin k, ∀ p ∈ S, χ p.2 = c

/--
Erdős Problem #8 (Disproved — Hough 2015):

The original conjecture (Erdős–Graham) asked: for any finite colouring of the integers,
is there a covering system all of whose moduli are monochromatic?

The answer is **no**, as a consequence of Hough's 2015 theorem that every covering
system must contain a modulus below an absolute bound (at most 10¹⁶, later improved
to 616000 by Balister, Bollobás, Morris, Sahasrabudhe, and Tiba 2022). One can
therefore assign a distinct colour to each integer up to this bound and a single
fresh colour to all larger integers; any covering system must then contain a small
modulus with a unique colour alongside potentially large moduli of the fresh colour,
making monochromaticity impossible.

Formally: there exists a finite colouring of the positive integers such that no
covering system has all its moduli the same colour.
-/
theorem erdos_problem_8 :
    ∃ k : ℕ, 0 < k ∧ ∃ χ : ℕ → Fin k,
      ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → ¬HasMonochromaticModuli χ S :=
  sorry
