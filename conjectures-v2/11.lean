import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

/--
Erdős Problem #11 [Er77c, ErGr80 p.28, Er85c, Er90, Er92c, Er97, Er97e, Er97f]:

Is every large odd integer n the sum of a squarefree number and a power of 2?

**Status**: OPEN — the page banner is FALSIFIABLE ("Open, but could be
disproved with a finite counterexample." — erdosproblems.com/11, page edition
20 January 2026, accessed 2026-03-05; the teorth/erdosproblems metadata
mirror agrees: state open, last update 2026-03-14). This theorem states the
conjectured "yes" direction of the question as a direct assertion. The
upstream formal-conjectures file (`ErdosProblems/11.lean`, `erdos_11`,
category `research open`) is also a direct assertion but of the stronger
form "every odd n > 1" — reasonable given Hercher's verification below —
whereas this file keeps the page's literal "every large odd integer"
(∃ N, ∀ n ≥ N).

Conventions: `2 ^ k` with `k : ℕ` allows 2^0 = 1 as a power of 2, matching
the upstream encoding (and the explicit "k, l ≥ 0" of the sibling problem
#9). The conjunct `s > 0` is redundant: Mathlib's `Squarefree` is false at 0
(`not_squarefree_zero`), so any witness is automatically positive; it is
kept from the first pass as harmless documentation of intent.

**Known partial results** (from the problem page):
- Odlyzko has checked this up to 10^7. Hercher [He24b] has verified it for
  all odd integers up to 2^50 ≈ 1.12 × 10^15 (formalized below as
  `erdos_problem_11.variants.hercher_range`).
- Granville and Soundararajan [GrSo98] have proved that this is very related
  to the problem of finding Wieferich primes (primes p with
  2^(p-1) ≡ 1 mod p²): if every odd integer is the sum of a squarefree
  number and a power of 2, then a positive proportion of primes are
  non-Wieferich primes (a weakened, density-free consequence is formalized
  below as `erdos_problem_11.variants.granville_soundararajan`).
- Erdős often asked this under the weaker assumption that n is not divisible
  by 4 (formalized below as `erdos_problem_11.variants.not_div_four`).
- Erdős thought that proving this with two powers of 2 is perhaps easy
  (formalized below as `erdos_problem_11.variants.two_powers`), and could
  prove that it is true (with a single power of two) for almost all n (not
  formalized here: an almost-all statement needs density machinery not
  present under this file's imports).

Related OEIS sequences: A001220 (Wieferich primes), A377587. See also
problems #9, #10, and #16. This is mentioned in problem A19 of Guy's
collection [Gu04]. Tags: number theory, additive basis.

References ([GrSo98] as it appears in the upstream formal-conjectures file
for this problem; [ErGr80] and [Gu04] from sibling files in this repository;
the site's /latex/11 and /bibs payloads were not captured in the session
logs, so the remaining keys carry no bibliographic data — DEFERRED, not
fabricated):
- [GrSo98] Granville, A. and Soundararajan, K., _A Binary Additive Problem
  of Erdős and the Order of 2 mod p²_. The Ramanujan Journal (1998),
  283-298.
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980). Cited by the page as [ErGr80, p.28].
- [Gu04] Guy, Richard K., _Unsolved problems in number theory_. 3rd ed.,
  Springer (2004), xviii+437. Problem A19.
- [He24b] Hercher (2024) — source of the 2^50 verification; title/venue not
  recovered.
- [Er77c], [Er85c], [Er90], [Er92c], [Er97], [Er97e], [Er97f] — keys only.
-/
theorem erdos_problem_11 :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → Odd n →
      ∃ (s k : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k :=
  sorry

/--
Erdős Problem #11, weaker-hypothesis variant (OPEN): from the problem page,
"Erdős often asked this under the weaker assumption that n is not divisible
by 4." The hypothesis 4 ∤ n is weaker than oddness (every odd n satisfies
it), so this statement is stronger than `erdos_problem_11`. Upstream
formal-conjectures has this as `erdos_11.variants.not_four_dvd` (for every
n > 1 with 4 ∤ n); as with the main statement, this file keeps the "every
large n" form.
-/
theorem erdos_problem_11.variants.not_div_four :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ¬(4 ∣ n) →
      ∃ (s k : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k :=
  sorry

/--
Erdős Problem #11, two-powers variant (OPEN): is every large odd integer the
sum of a squarefree number and two powers of 2? From the problem page:
"Erdős thought that proving this with two powers of 2 is perhaps easy." No
proof is recorded on the page, and upstream formal-conjectures also carries
it as open (`erdos_11.variants.two_pow_two`).
-/
theorem erdos_problem_11.variants.two_powers :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → Odd n →
      ∃ (s k l : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k + 2 ^ l :=
  sorry

/--
Erdős Problem #11, verified range (SOLVED, computational): every odd n with
1 < n < 2^50 is the sum of a squarefree number and a power of 2 — Hercher
[He24b] ("has verified this is true for all odd integers up to
2^50 ≈ 1.12 × 10^15"); this subsumes Odlyzko's earlier check up to 10^7.

Notes: n = 1 is genuinely not representable (s ≥ 1 and 2^k ≥ 1 force
s + 2^k ≥ 2), so the guard 1 < n is required for the page's "all odd
integers up to 2^50" to be literally true; and since 2^50 is even, `n < 2^50`
and "up to 2^50" agree on odd n. Upstream formal-conjectures carries the
same two statements as `erdos_11.variants.finite_bound1` (10^7) and
`erdos_11.variants.finite_bound2` (2^50).
-/
theorem erdos_problem_11.variants.hercher_range :
    ∀ n : ℕ, Odd n → 1 < n → n < 2 ^ 50 →
      ∃ (s k : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k :=
  sorry

/--
Erdős Problem #11, Granville–Soundararajan consequence (SOLVED implication,
[GrSo98]): if every odd n > 1 is the sum of a squarefree number and a power
of 2, then there are infinitely many non-Wieferich primes, i.e. primes p
with 2^(p-1) ≢ 1 (mod p²). From the problem page: "if every odd integer is
the sum of a squarefree number and a power of 2 then a positive proportion
of primes are non-Wieferich primes."

Faithfulness notes:
- The page's conclusion is the stronger "a positive proportion of primes";
  positive proportion implies infinitude, and infinitude ("for every m there
  is a non-Wieferich prime p ≥ m") is what is encoded here, because
  relative-density machinery is not available under this file's imports.
  Even the infinitude of non-Wieferich primes is not known unconditionally,
  so the weakened conclusion is still substantive.
- The hypothesis quantifies over all odd n > 1 (the page's "every odd
  integer"; n = 1 is not representable), not merely all large n.
- ℕ-subtraction guard: `p - 1` does not truncate, since `Nat.Prime p` gives
  p ≥ 2. The prime p = 2 satisfies 2^1 % 2^2 = 2 ≠ 1 and so counts as
  non-Wieferich here — consistent with the usual convention and harmless
  for an infinitude statement.
- The upstream formal-conjectures variant
  (`erdos_11.variants.granville_soundararajan`) instead concludes
  `{p | p.Prime ∧ 2 ^ p ≡ 2 [MOD p ^ 2]}.Infinite`, which for odd p is the
  set of *Wieferich* primes — the opposite polarity from the page's
  "non-Wieferich". This file follows the page's direction; see the review
  (`fable-review/11.md`) for the derivation. Verification against the text
  of [GrSo98] itself is DEFERRED (offline).
-/
theorem erdos_problem_11.variants.granville_soundararajan
    (H : ∀ n : ℕ, Odd n → 1 < n →
      ∃ (s k : ℕ), Squarefree s ∧ s > 0 ∧ n = s + 2 ^ k) :
    ∀ m : ℕ, ∃ p : ℕ, m ≤ p ∧ Nat.Prime p ∧ 2 ^ (p - 1) % p ^ 2 ≠ 1 :=
  sorry
