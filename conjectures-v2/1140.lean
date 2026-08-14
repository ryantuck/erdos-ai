import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Erdos1140

/-!
# Erdős Problem #1140

Do there exist infinitely many $n$ such that $n - 2x^2$ is prime for all $x$
with $2x^2 < n$?

Verbatim source statement (erdosproblems.com/1140): "Do there exist infinitely
many $n$ such that $n-2x^2$ is prime for all $x$ with $2x^2<n$?"

Status: DISPROVED per erdosproblems.com/1140 (page last edited 26 January 2026,
accessed 2026-02-23) — "This has been solved in the negative."

The known such $n$ are $2, 5, 7, 13, 31, 61, 181, 199$, and it is known that
these are, with at most one exception, all such $n$; in particular the set of
such $n$ is finite and the answer to the question is "no". Theorem 4.1 of
Epure and Gica [EpGi10] implies that the only such $n \equiv 1 \pmod{4}$ are
$5, 13, 61, 181$. Epure and Gica also remark that their method, coupled with a
result of Mollin and Williams [MoWi89], implies that the only such
$n \equiv 3 \pmod{4}$ are $7, 31, 199$, and at most one other exception.
(Even $n$ must equal $2$, since taking $x = 0$ forces $n$ itself to be prime.)

The problem is a yes/no question that has been solved in the negative;
the main theorem below states the true ("no") direction as a direct assertion
of finiteness. In styled question form it would be
`answer(False) ↔ Set.Infinite {n : ℕ | AllShiftsArePrime n}`, which is how the
upstream formal-conjectures file states it (an equivalent encoding, via
`Set.not_infinite`).

See also: problem #1141.
Tags: number theory
Related OEIS sequences: none listed (the database marks them "Possible").
Additional thanks (per the page): Wouter van Doorn.

Reference: [Va99, 1.5]
https://www.erdosproblems.com/1140

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999),
  §1.5. (Honest stub from the upstream contributing guide's canonical entry
  for this key, consistent with sibling files 1068, 1131, 1132, 1137, 1138,
  1139; fuller bibliographic detail is DEFERRED. Note: the "Vaughan, R. C.,
  *The Hardy-Littlewood Method*, 2nd ed., 1997" attribution carried by this
  problem's styled artifact and endorsed by its prior AI review is a
  hallucination for this key and is deliberately not reproduced here.)

[EpGi10] Epure and Gica, _Principal quadratic real fields in connection with
  some additive problems_. Bull. Math. Soc. Sci. Math. Roumanie (N.S.) (2010),
  251-259. (Title, journal, and pages from the original pipeline's fetch of
  erdosproblems.com/latex/1140; the volume number was not captured and is
  DEFERRED. Author first names/initials conflict between captures — the /latex
  extraction gives "Epure, Mihai and Gica, Alexandru", the styled artifact and
  prior AI review give "Epure, R. and Gica, A." — so only surnames are
  recorded here.)

[MoWi89] Mollin, R. A. and Williams, H. C., _Period four and real quadratic
  fields of class number one_. Proc. Japan Acad. Ser. A Math. Sci. (1989),
  89-93. (Title, journal, and pages from the original pipeline's fetch of
  erdosproblems.com/latex/1140; the volume number was not captured and is
  DEFERRED.)
-/

/-- The property that n - 2x² is prime for all x with 2x² < n.

Encoding notes:
* Quantifying `x` over all of ℕ (including `x = 0`) is load-bearing: `x = 0`
  forces `n` itself to be prime, which is what pins the qualifying set to the
  source's known list {2, 5, 7, 13, 31, 61, 181, 199} (starting from `x = 1`
  would wrongly admit e.g. 4, 15, 21, 25, 49, …).
* The strict inequality `2 * x ^ 2 < n` is likewise load-bearing: a non-strict
  `≤` would demand `Nat.Prime 0` at `n = 2 * x ^ 2` and wrongly exclude `n = 2`.
* The ℕ subtraction `n - 2 * x ^ 2` never truncates, being guarded by
  `2 * x ^ 2 < n`.
* Degenerate case: `AllShiftsArePrime 0` holds vacuously (no `x` satisfies
  `2 * x ^ 2 < 0`), so `0` is a spurious member of
  `{n : ℕ | AllShiftsArePrime n}` not intended by the source. This is harmless
  for the finiteness assertion below (it changes the set by one element), and
  the positivity guard in the completeness variant excludes it. -/
def AllShiftsArePrime (n : ℕ) : Prop :=
  ∀ x : ℕ, 2 * x ^ 2 < n → Nat.Prime (n - 2 * x ^ 2)

/--
Erdős Problem #1140 [Va99, 1.5] (Disproved):

Do there exist infinitely many n such that n - 2x² is prime for all x
with 2x² < n?

The known such n are 2, 5, 7, 13, 31, 61, 181, 199. Theorem 4.1 of Epure and
Gica [EpGi10] implies that the only such n ≡ 1 (mod 4) are 5, 13, 61, 181;
Epure and Gica also remark that their method, coupled with a result of Mollin
and Williams [MoWi89], implies that the only such n ≡ 3 (mod 4) are 7, 31, 199,
and at most one other exception. Since even such n must equal 2 (take x = 0),
the list above is, with at most one exception, complete — in particular the set
of such n is finite, answering the question in the negative.

Tags: number theory
-/
theorem erdos_problem_1140 :
    Set.Finite {n : ℕ | AllShiftsArePrime n} :=
  sorry

/--
Variant (page-confirmed known solutions): each of 2, 5, 7, 13, 31, 61, 181, 199
satisfies the property — "The known such n are 2, 5, 7, 13, 31, 61, 181, 199."
(A finite decidable check; verified numerically during review.)
-/
theorem erdos_problem_1140.variants.known_solutions :
    ∀ n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ), AllShiftsArePrime n :=
  sorry

/--
Variant (Epure-Gica [EpGi10], Theorem 4.1): the only such n ≡ 1 (mod 4) are
5, 13, 61, 181. Solved, unconditional per the source page.
-/
theorem erdos_problem_1140.variants.mod_four_one :
    ∀ n : ℕ, n % 4 = 1 → AllShiftsArePrime n → n ∈ ({5, 13, 61, 181} : Set ℕ) :=
  sorry

/--
Variant (Epure-Gica [EpGi10] coupled with Mollin-Williams [MoWi89]): the only
such n ≡ 3 (mod 4) are 7, 31, 199, and at most one other exception — encoded as
the existence of a single value m outside of which no further n ≡ 3 (mod 4)
qualifies (if there is no exception, any junk witness m works).
-/
theorem erdos_problem_1140.variants.mod_four_three :
    ∃ m : ℕ, ∀ n : ℕ, n % 4 = 3 → AllShiftsArePrime n →
      n ∈ ({7, 31, 199} : Set ℕ) ∨ n = m :=
  sorry

/--
Variant (page-confirmed completeness): "It is known that these are, with at
most one exception, all such n" — every positive n with the property lies in
the known list, with at most one exception. The guard 0 < n excludes the
vacuous member n = 0 (see `AllShiftsArePrime`), which the source does not
count and which would otherwise be forced to play the role of the exception.
-/
theorem erdos_problem_1140.variants.at_most_one_exception :
    ∃ m : ℕ, ∀ n : ℕ, 0 < n → AllShiftsArePrime n →
      n ∈ ({2, 5, 7, 13, 31, 61, 181, 199} : Set ℕ) ∨ n = m :=
  sorry

end Erdos1140
