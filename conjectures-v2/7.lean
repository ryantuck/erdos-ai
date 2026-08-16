import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Ring.Parity

/--
A finite system of congruences `{(aᵢ, mᵢ)}` is a **covering system** if every
modulus is positive and every integer satisfies at least one congruence `n ≡ aᵢ (mod mᵢ)`.

Note: this predicate alone requires neither distinct moduli (see
`HasDistinctModuli`) nor moduli greater than one. Erdős's standard notion of a
covering system [ErGr80] requires both: moduli `1 < m₁ < m₂ < ⋯ < mₖ`. The
modulus-one exclusion matters for Problem #7: the singleton system
`{(0, 1)}` (everything ≡ 0 (mod 1)) satisfies this predicate, has distinct
moduli, and its only modulus is odd — so an existence statement over this
predicate without a `1 < mᵢ` hypothesis is trivially true and does not encode
the problem. (The same encoding of this predicate appears in the formalization
of Erdős Problem #2, where modulus one is instead harmless.)
-/
def IsCoveringSystem (S : Finset (ℤ × ℕ)) : Prop :=
  S.Nonempty ∧
  (∀ p ∈ S, 0 < p.2) ∧
  (∀ n : ℤ, ∃ p ∈ S, (p.2 : ℤ) ∣ (n - p.1))

/--
A covering system has **distinct moduli** if no two congruences share the same
modulus. This is part of the notion of covering system Erdős used [ErGr80];
the same encoding appears in the formalization of Erdős Problem #2.
-/
def HasDistinctModuli (S : Finset (ℤ × ℕ)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p.2 = q.2 → p = q

/--
Erdős Problem #7 (OPEN; status banner "VERIFIABLE — open, but could be proved
with a finite example"):

Is there a distinct covering system all of whose moduli are odd?

Asked by Erdős and Selfridge (sometimes also with Schinzel). A **distinct
covering system** is a finite collection of congruences `{n ≡ aᵢ (mod mᵢ)}`
with pairwise distinct moduli, **all greater than one**, covering every
integer. The question asks whether such a system can exist with all moduli
odd.

The hypothesis `1 < mᵢ` is essential and standard (Erdős's convention
`1 < m₁ < ⋯ < mₖ` [ErGr80]): without it the singleton system `{(0, 1)}` is a
covering system with distinct odd moduli, making the existence statement
trivially true instead of the open question. The same convention is needed for
the Hough–Nielsen theorem quoted below to be true as stated (the system
`{(0, 1)}` has no modulus divisible by 2 or 3).

Known results:
- Hough and Nielsen [HoNi19] proved that in any distinct covering system (with
  moduli greater than one), at least one modulus must be divisible by 2 or 3.
  A simpler proof was given by Balister, Bollobás, Morris, Sahasrabudhe, and
  Tiba [BBMST22], who also proved that if an odd covering system exists then
  the least common multiple of its moduli must be divisible by 9 or 15.
- [BBMST22] proved no odd distinct covering system exists if the moduli are
  additionally required to be squarefree (a stronger question also asked by
  Erdős and Selfridge). The general odd case remains open.
- Selfridge showed (as reported in [Sc67]) that an odd covering system exists
  if a covering system exists whose moduli n₁, …, nₖ are such that no nᵢ
  divides any other nⱼ — but the latter has been shown not to exist; see
  Erdős problem [586].
- Prize history, as reported by Filaseta, Ford, and Konyagin [FFK00]: Erdős,
  convinced that an odd covering does exist, offered $25 for a proof that none
  exists; Selfridge, convinced (at that point) of the opposite, offered $300 —
  later raised to $2000 — for the first explicit example. (The teorth/
  erdosproblems metadata mirror currently records no active prize; the page
  banner shows $25.)

Formalized as a direct assertion of the existence ("yes") direction — Erdős's
own conjectured direction, and the direction a finite example would verify;
the upstream formal-conjectures encoding is `answer(sorry) ↔` this same
existential. The problem is OPEN: this statement is a conjecture, not a known
theorem.

Source: erdosproblems.com/7 (page last edited 22 January 2026, accessed
2026-02-18); tags: number theory, covering systems; no related OEIS sequence.
Original sources on the page: [Er57], [Er61], [Er65], [Er65b], [Er73],
[ErGr80], [Er82e], [Er90], [Er95, p.166], [Er96b], [Er97], [Er97c], [Er97e].

References (recovered from erdosproblems.com/latex/7; volume/issue numbers
were absent from the recovered extraction and are deliberately omitted):
- [HoNi19] Hough, R. D. and Nielsen, P. P., Covering systems with restricted
  divisibility. Duke Mathematical Journal (2019), 3261-3295.
- [BBMST22] Balister, P., Bollobás, B., Morris, R., Sahasrabudhe, J., and
  Tiba, M., On the Erdős covering problem: the density of the uncovered set.
  Inventiones mathematicae (2022), 377-414.
- [Sc67] Schinzel, A., Reducibility of polynomials and covering systems of
  congruences. Acta Arithmetica (1967/68), 91-101.
- [FFK00] Filaseta, M., Ford, K., and Konyagin, S., On an irreducibility
  theorem of A. Schinzel associated with coverings of the integers. Illinois
  Journal of Mathematics (2000), 633-643.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
-/
theorem erdos_problem_7 :
    ∃ S : Finset (ℤ × ℕ),
      IsCoveringSystem S ∧
      HasDistinctModuli S ∧
      (∀ p ∈ S, 1 < p.2) ∧
      (∀ p ∈ S, Odd p.2) :=
  sorry

/--
Erdős Problem #7, Hough–Nielsen theorem [HoNi19]:

In any covering system with distinct moduli, all greater than one, at least
one modulus must be divisible by 2 or 3. (A simpler proof was later given in
[BBMST22].) The `1 < mᵢ` hypothesis is essential: `{(0, 1)}` would otherwise
be a counterexample.
-/
theorem erdos_problem_7.variants.hough_nielsen :
    ∀ S : Finset (ℤ × ℕ),
      IsCoveringSystem S → HasDistinctModuli S → (∀ p ∈ S, 1 < p.2) →
      ∃ p ∈ S, 2 ∣ p.2 ∨ 3 ∣ p.2 :=
  sorry

/--
Erdős Problem #7, squarefree case [BBMST22]:

Erdős and Selfridge also asked whether there can be a covering system all of
whose moduli are odd and squarefree. Balister, Bollobás, Morris, Sahasrabudhe,
and Tiba proved the answer is no. Squarefreeness of a natural number `m` is
encoded inline as `∀ d : ℕ, d * d ∣ m → d = 1`, which for ℕ agrees with
Mathlib's `Squarefree` (whose `IsUnit d` is `d = 1` on ℕ); the inline form
avoids an extra import in this unverified-compile pipeline. Both the
distinctness and the `1 < mᵢ` hypotheses are essential: without them
`{(0, 1)}` and the complete residue system `{(0, 3), (1, 3), (2, 3)}` would
be odd squarefree covering systems.
-/
theorem erdos_problem_7.variants.bbmst_squarefree :
    ¬ ∃ S : Finset (ℤ × ℕ),
      IsCoveringSystem S ∧
      HasDistinctModuli S ∧
      (∀ p ∈ S, 1 < p.2) ∧
      (∀ p ∈ S, Odd p.2) ∧
      (∀ p ∈ S, ∀ d : ℕ, d * d ∣ p.2 → d = 1) :=
  sorry

/--
Erdős Problem #7, lcm condition [BBMST22]:

Balister, Bollobás, Morris, Sahasrabudhe, and Tiba proved that if an odd
covering system (distinct moduli, all greater than one) exists, then the least
common multiple of its moduli must be divisible by 9 or 15. Stated here in an
equivalent pointwise form avoiding `Finset.lcm` (not available under the
current imports): for positive integers, `9 ∣ lcm` iff some modulus is
divisible by `9 = 3²` (the 3-adic valuation of the lcm is the maximum of the
moduli's), and `15 ∣ lcm` iff some modulus is divisible by 3 and some modulus
is divisible by 5.
-/
theorem erdos_problem_7.variants.bbmst_lcm :
    ∀ S : Finset (ℤ × ℕ),
      IsCoveringSystem S → HasDistinctModuli S → (∀ p ∈ S, 1 < p.2) →
      (∀ p ∈ S, Odd p.2) →
      ((∃ p ∈ S, 9 ∣ p.2) ∨ ((∃ p ∈ S, 3 ∣ p.2) ∧ (∃ p ∈ S, 5 ∣ p.2))) :=
  sorry
