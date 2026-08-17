import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

/--
A finite system of congruences `{(aᵢ, mᵢ)}` is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence `n ≡ aᵢ (mod mᵢ)`.

Note: this predicate alone does not require the moduli to be distinct, nor does
it exclude the modulus 1. Erdős's usage of "covering system" (cf. [ErGr80])
requires distinct moduli `1 < m₁ < m₂ < … < mₖ` — see `HasDistinctModuli`
below and the `1 < p.2` hypothesis in the theorem. Without those constraints
the complete residue system `{(0, m), (1, m), …, (m − 1, m)}` (all moduli
equal to `m`), and the single congruence `{(0, 1)}` (everything ≡ 0 (mod 1)),
are admitted; both are trivially monochromatic under any colouring and would
make the theorem below false as stated.
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
A covering system has **distinct moduli** if no two congruences share the same
modulus. This is the notion of covering system Erdős used [ErGr80]; the same
encoding appears in the formalization of Erdős Problem #7.
-/
def HasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q

/--
All moduli in a covering system are **monochromatic** under a colouring `χ : ℕ → Fin k`
if there exists a colour `c` such that every modulus in `S` receives colour `c`.
-/
def HasMonochromaticModuli {k : ℕ} (χ : ℕ → Fin k) (S : Finset (ℤ × ℕ)) : Prop :=
  ∃ c : Fin k, ∀ p ∈ S, χ p.2 = c

/--
Erdős Problem #8 (DISPROVED — Hough 2015):

The original conjecture (Erdős–Graham [ErGr80, p.25]) asked: for any finite
colouring of the integers, is there a covering system all of whose moduli are
monochromatic?

The answer is **no**, as a consequence of Hough's theorem [Ho15] that every
covering system (in Erdős's sense: distinct moduli, all `> 1`) must contain a
modulus below an absolute bound (at most 10¹⁶, later improved to 616000 by
Balister, Bollobás, Morris, Sahasrabudhe, and Tiba [BBMST22]). As the problem
page puts it, "one could colour all integers < 10¹⁸ different colours and all
other integers a new colour": any qualifying covering system contains a modulus
`m ≤ 10¹⁶`, whose colour is shared by no other modulus, so monochromaticity
would force every modulus to equal `m` — impossible for a distinct-moduli
system, since a single congruence with modulus `m > 1` does not cover ℤ.

Formally (the true, resolved direction): there exists a finite colouring of the
positive integers such that no covering system with distinct moduli `> 1` has
all its moduli the same colour.

Both side conditions are essential, not stylistic:
- without `HasDistinctModuli`, the complete residue system
  `{(0, 2), (1, 2)}` is a covering system whose moduli are trivially
  monochromatic (single modulus value 2) under *any* colouring;
- without `1 < p.2`, the singleton `{(0, 1)}` has distinct moduli, covers ℤ,
  and is again trivially monochromatic.
Either degeneracy makes the un-hypothesised statement false for every
colouring, inverting the intended answer.

Erdős and Graham also asked a density-type version: is
`∑_{a ∈ A, a > N} 1/a ≫ log N` a sufficient condition for `A` to contain the
moduli of a covering system? Hough's theorem answers this negatively as well.
(Not formalized here: it needs real-valued sums and `log`, machinery not
present in this file.)

Source: erdosproblems.com/8 (page edition 28 December 2025, accessed
2026-02-18); status DISPROVED ("This has been solved in the negative.");
tags: number theory, covering systems. Original sources on the page:
[ErGr80, p.25], [Er96b], [Er97], [Er97e]; the remarks cite [Ho15].

References ([Ho15] and [BBMST22] recovered from the erdosproblems.com/latex/2
extraction for the same papers; volume/issue numbers were absent from the
recovered extraction and are deliberately omitted; [Er96b], [Er97], [Er97e]
bibliographic data was not recoverable — keys only):
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
- [Ho15] Hough, B., Solution of the minimum modulus problem for covering
  systems. Annals of Mathematics (2) (2015), 361-382.
- [BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and
  Tiba, M., On the Erdős covering problem: the density of the uncovered set.
  Inventiones mathematicae (2022), 377-414.
-/
theorem erdos_problem_8 :
    ∃ k : ℕ, 0 < k ∧ ∃ χ : ℕ → Fin k,
      ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → HasDistinctModuli S →
        (∀ p ∈ S, 1 < p.2) → ¬HasMonochromaticModuli χ S :=
  sorry

/--
Erdős Problem #8, explicit colouring from the problem page's remark:

colouring the integers below 10¹⁸ with pairwise different colours and all
larger integers with one further colour (10¹⁸ + 1 colours in total) defeats
every covering system with distinct moduli `> 1`, since by Hough's theorem
[Ho15] such a system contains a modulus at most 10¹⁶ < 10¹⁸, whose colour no
other modulus can share.
-/
theorem erdos_problem_8.variants.explicit_colouring :
    ∃ χ : ℕ → Fin (10 ^ 18 + 1),
      ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → HasDistinctModuli S →
        (∀ p ∈ S, 1 < p.2) → ¬HasMonochromaticModuli χ S :=
  sorry
