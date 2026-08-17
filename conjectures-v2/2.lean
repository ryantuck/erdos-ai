import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic

/--
A finite system of congruences `{(aᵢ, mᵢ)}` is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence `n ≡ aᵢ (mod mᵢ)`.

Note: this predicate alone does not require the moduli to be distinct. Erdős's
minimum-modulus problem concerns covering systems with *distinct* moduli (his
standard usage, cf. [ErGr80]) — see `HasDistinctModuli` below. Without
distinctness the complete residue system `{(0, m), (1, m), …, (m − 1, m)}`
covers ℤ with every modulus equal to `m`, so the smallest modulus could
trivially be made arbitrarily large.
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
Erdős Problem #2 (DISPROVED; $1000 prize):

Can the smallest modulus of a covering system be arbitrarily large?

Erdős described this as "perhaps my favourite problem" and expected the answer
to be yes. Hough [Ho15] (2015), building on work of Filaseta, Ford, Konyagin,
Pomerance, and Yu [FFKPY07], showed the answer is **no**: every covering system
(with distinct moduli) has smallest modulus at most 10¹⁶. Balister, Bollobás,
Morris, Sahasrabudhe, and Tiba [BBMST22] gave a simpler proof and improved the
bound to 616000. The best known lower bound is a covering system whose minimum
modulus is 42, due to Owens [Ow14].

Formally (the true, resolved direction): there exists an absolute constant B
such that every covering system with distinct moduli contains a congruence
whose modulus is at most B.

The distinct-moduli hypothesis is essential: without it, for any B the complete
residue system mod (B + 1), i.e. `{(0, B+1), …, (B, B+1)}`, is a covering
system all of whose moduli exceed B, and the statement would be false. With
distinct moduli the system `{(0, 1)}` (everything ≡ 0 (mod 1)) is still
admitted; it has smallest modulus 1 and is harmless to this bounded-modulus
statement.

Source: erdosproblems.com/2 (page edition 23 January 2026, accessed
2026-02-17); status DISPROVED ("This has been solved in the negative."), tags:
number theory, covering systems. Original sources on the page: [Er55c], [Er57],
[Er61], [Er65], [Er65b], [Er73], [Er77c], [ErGr80, p.24], [Er82e], [Er85c],
[Er90], [Er95, p.166], [Er96b], [Er97], [Er97c], [Er97e], [Va99, 1.31].
Related OEIS sequence: A160559.

References (recovered from erdosproblems.com/latex/2; volume/issue numbers
were absent from the recovered extraction and are deliberately omitted):
- [Ho15] Hough, B., Solution of the minimum modulus problem for covering
  systems. Annals of Mathematics (2) (2015), 361-382.
- [FFKPY07] Filaseta, M., Ford, K., Konyagin, S., Pomerance, C., and Yu, G.,
  Sieving by large integers and covering systems of congruences. J. Amer.
  Math. Soc. (2007), 495-517.
- [BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and
  Tiba, M., On the Erdős covering problem: the density of the uncovered set.
  Inventiones mathematicae (2022), 377-414.
- [Ow14] Owens, T., A Covering System with Minimum Modulus 42. Thesis,
  Brigham Young University (2014).
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
-/
theorem erdos_problem_2 :
    ∃ B : ℕ, ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → HasDistinctModuli S →
      ∃ p ∈ S, p.2 ≤ B :=
  sorry

/--
Erdős Problem #2, Hough's original bound [Ho15]:

Hough proved that every covering system with distinct moduli contains a
modulus at most 10¹⁶.
-/
theorem erdos_problem_2.variants.hough_bound :
    ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → HasDistinctModuli S →
      ∃ p ∈ S, p.2 ≤ 10 ^ 16 :=
  sorry

/--
Erdős Problem #2, best known upper bound [BBMST22]:

Balister, Bollobás, Morris, Sahasrabudhe, and Tiba proved that every covering
system with distinct moduli contains a modulus at most 616000.
-/
theorem erdos_problem_2.variants.bbmst_bound :
    ∀ S : Finset (ℤ × ℕ), IsCoveringSystem S → HasDistinctModuli S →
      ∃ p ∈ S, p.2 ≤ 616000 :=
  sorry

/--
Erdős Problem #2, best known lower bound [Ow14]:

Owens constructed a covering system with distinct moduli whose minimum modulus
is exactly 42 — the best known lower bound for the largest possible minimum
modulus of a covering system.
-/
theorem erdos_problem_2.variants.owens_lower_bound :
    ∃ S : Finset (ℤ × ℕ), IsCoveringSystem S ∧ HasDistinctModuli S ∧
      (∀ p ∈ S, 42 ≤ p.2) ∧ (∃ p ∈ S, p.2 = 42) :=
  sorry
