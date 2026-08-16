import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic

open Nat

noncomputable section

/--
The prime gap at index n: d(n) = p_{n+1} - p_n, where p_k is the k-th prime
in Mathlib's 0-indexed convention (`nth Nat.Prime 0 = 2`, `nth Nat.Prime 1 = 3`, …),
so `primeGap n` is the source's d_{n+1} in the usual 1-indexed convention.

The subtraction is ℕ subtraction, but it never truncates: `Nat.Prime` is an
infinite predicate, so `nth Nat.Prime` is strictly monotone and
`nth Nat.Prime (n + 1) > nth Nat.Prime n` for every n.
-/
def primeGap (n : ℕ) : ℕ :=
  nth Nat.Prime (n + 1) - nth Nat.Prime n

/--
Erdős Problem #6 [Er55c, Er57, Er61, Er65b, Er77c, Er79, Er79d, ErGr80, Er85c, Er90]:

Let d_n = p_{n+1} - p_n. Are there infinitely many n such that d_n < d_{n+1} < d_{n+2}?

SOLVED in the affirmative (erdosproblems.com status: PROVED, $100 prize; page
last edited 28 September 2025, accessed 2026-02-18; status cross-checked
"proved" against the teorth/erdosproblems metadata mirror, last update
2025-08-31). The statement below asserts the affirmed direction directly.

Conjectured by Erdős and Turán [ErTu48]. Erdős offered $25000 for a
*disproof*, while commenting that the conjecture "is certainly true" (in
[Er85c] he goes further and offers "all the money I can earn, beg, borrow or
steal" for a disproof). Proved by Banks, Freiberg, and Turnage-Butterbaugh
[BFT15] (2015) using the Maynard–Tao machinery on bounded gaps between
primes [Ma15]. They showed that for any m ≥ 1 there are infinitely many n
with d_n < d_{n+1} < ⋯ < d_{n+m}, and infinitely many n with
d_n > d_{n+1} > ⋯ > d_{n+m} (see variants below). This is discussed in
problem A11 of Guy's collection [Gu04].

Here `nth Nat.Prime` is 0-indexed (p₀ = 2, p₁ = 3, …), so Lean index n is the
source's 1-indexed n + 1; this reindexing is a bijection on witnesses, so
"infinitely many" is preserved exactly, with no degenerate boundary cases.

Related OEIS sequence: A335277 (start of first run of n consecutive ascending
prime gaps). Tags: number theory, primes.

References (recovered from the archived page, the upstream formal-conjectures
file capture, and sibling files in this repo; entries marked "stub" lack full
data, which is DEFERRED, not fabricated — see erdosproblems.com/latex/6):
- [Er55c] Erdős, P., Some problems on number theory (1955). (stub)
- [Er57] Erdős, P., Some unsolved problems (1957). (stub)
- [Er61] Erdős, P., Some unsolved problems. Magyar Tud. Akad. Mat. Kutató
  Int. Közl. 6 (1961), 221-254.
- [Er65b] Erdős, P., Some recent advances and current problems in number
  theory. Lectures on Modern Mathematics III (1965), 196-244. (sibling files
  disagree on the title of this key)
- [Er77c] Erdős, P., Problems and results on combinatorial number theory.
  III. Number Theory Day (Proc. Conf., Rockefeller Univ., New York, 1976)
  (1977), 43-72.
- [Er79] Erdős, P., Some unconventional problems in number theory (1979).
  (stub; sibling files split the venue between Acta Math. Acad. Sci. Hungar.
  33 (1979), 71-80 and Math. Mag. 52 (1979), 67-70)
- [Er79d] Erdős, P., Some unconventional problems in number theory.
  Math. Mag. 52 (1979), 67-70. (majority sibling entry; one sibling assigns
  the Acta Math. Acad. Sci. Hungar. venue to this key instead)
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathematique
  (1980).
- [Er85c] Erdős, P. (1985). (stub; sibling files disagree on the title; one
  sibling gives the venue Number theory (Ootacamund, 1984) (1985), 74-84)
- [Er90] Erdős, P., Some of my favourite unsolved problems. A tribute to
  Paul Erdős (1990), 467-478.
- [ErTu48] Erdős, P. and Turán, P. (1948). (stub; key from the page remarks,
  no bibliographic data recoverable offline)
- [BFT15] Banks, William D., Freiberg, Tristan, and Turnage-Butterbaugh,
  Caroline L., Consecutive primes in tuples. Acta Arith. (2015), 261-266.
  (verbatim from the upstream formal-conjectures ErdosProblems/6.lean
  capture)
- [Ma15] Maynard, James, Small gaps between primes. Ann. of Math. (2)
  (2015), 383-413. (same provenance)
- [Gu04] Guy, R. K., Unsolved problems in number theory (2004), xviii+437.
-/
theorem erdos_problem_6 :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      primeGap n < primeGap (n + 1) ∧
      primeGap (n + 1) < primeGap (n + 2) :=
  sorry

/--
Erdős Problem #6, increasing runs of prime gaps [BFT15]:

Banks, Freiberg, and Turnage-Butterbaugh proved that for any m ≥ 1 there are
infinitely many n such that d_n < d_{n+1} < ⋯ < d_{n+m}. The chain of m
strict inequalities over the gaps at indices n, …, n + m is encoded as
∀ i < m, d_{n+i} < d_{n+i+1}. The case m = 2 is the main problem above.
(The hypothesis 1 ≤ m mirrors the page's "for any m ≥ 1"; for m = 0 the
inner condition would be vacuously true.)
-/
theorem erdos_problem_6.variants.increasing (m : ℕ) (hm : 1 ≤ m) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      ∀ i : ℕ, i < m → primeGap (n + i) < primeGap (n + i + 1) :=
  sorry

/--
Erdős Problem #6, decreasing runs of prime gaps [BFT15]:

Banks, Freiberg, and Turnage-Butterbaugh also proved the mirror statement:
for any m ≥ 1 there are infinitely many n such that
d_n > d_{n+1} > ⋯ > d_{n+m}, encoded as ∀ i < m, d_{n+i} > d_{n+i+1}.
-/
theorem erdos_problem_6.variants.decreasing (m : ℕ) (hm : 1 ≤ m) :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      ∀ i : ℕ, i < m → primeGap (n + i + 1) < primeGap (n + i) :=
  sorry

end
