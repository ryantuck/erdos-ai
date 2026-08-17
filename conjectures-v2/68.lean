import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Erdős Problem 68

*Reference:* [erdosproblems.com/68](https://www.erdosproblems.com/68)
(accessed 2026-03-05; page edition "last edited 28 September 2025"; page content
recovered from the archived capture in the original pipeline session's log,
`claude-session-logs/5cc22e56-bf7b-446d-b01e-8ced34c1f7a7.jsonl` line 12, a Read of
the then-extant `tidy/68.html` — the live site is unreachable from the review
container).

Statement (verbatim from the site): "Is $$\sum_{n\geq 2}\frac{1}{n!-1}$$
irrational?" Cited on the page as [Er68d][Er88c,p.102][Er90][Er97e][Er97f]. Tags:
number theory | irrationality. No prize. The decimal expansion of the sum is OEIS
A331373.

Status: **OPEN** (tooltip: "This is open, and cannot be resolved with a finite
computation."). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
commit a09c7a2, 2026-08-14) agrees: open, last update 2025-08-31, OEIS A331373. The
upstream google-deepmind/formal-conjectures repository (HEAD dd1c2beb, fetched
2026-08-16) has `ErdosProblems/68.lean` with `@[category research open]` and
`answer(sorry) ↔ Irrational (∑' n : ℕ, 1 / ((n + 2).factorial - 1 : ℝ))`, matching
the page's "Formalised statement? Yes" link.

Remarks from the page: "The decimal expansion is A331373 in the OEIS. Weisenberg has
observed that this sum can also be written as
$$\sum_{k\geq 1}\sum_{n\geq 2}\frac{1}{(n!)^k}.$$ Erdős [Er88c] notes that
$\sum \frac{1}{n!+t}$ should be transcendental for every integer $t$." Additional
thanks (per the page): Desmond Weisenberg.

The Weisenberg identity is formalized as a variant below (upstream proves it as a
`textbook`-category lemma, `sum_factorial_inv_eq_geometric`). The transcendence note
is deliberately left as prose: `Transcendental` would require imports and constructs
not otherwise in this file, and the page records it as an expectation ("should be"),
not a theorem.

References (per-entry provenance; the page's `/latex/68` and `/bibs/` payloads were
NOT captured in the logs, so entries below are corpus-consensus or key-only stubs,
marked DEFERRED — nothing is fabricated):

- [Er68d] Erdős, P. (1968). (Key-only stub: no expansion of this key is recoverable
  offline — no sibling file in this corpus expands it, and no `/latex` capture
  carries it; DEFERRED.)
- [Er88c] Erdős, P., _On the irrationality of certain series: problems and results_.
  New advances in transcendence theory (Durham, 1986) (1988), 102-109.
  (Corpus-consensus entry, e.g. `deepmind/deepmind/1050.lean`,
  `deepmind/deepmind/262.lean`; the page's pin [Er88c, p.102] falls on this entry's
  page range, corroborating it. A minority of sibling files carry a different title
  for this key; DEFERRED.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
  Erdős (1990), 467-478. (Corpus-consensus entry across many sibling files;
  DEFERRED.)
- [Er97e] Erdős, P. (1997). (Key-only stub: sibling corpus expansions conflict —
  "Some of my favourite problems which recently have been solved", Proc. Int. Conf.
  on Discrete Math. (1997), 527-537 (`deepmind/deepmind/654.lean`), vs "Some
  problems and results on combinatorial number theory"
  (`deepmind/deepmind/91.lean`); DEFERRED.)
- [Er97f] Erdős, P. (1997). (Key-only stub: sibling corpus expansions conflict —
  "Some unsolved problems", Combinatorics, geometry and probability (Cambridge,
  1993) (1997), 1-10 (`deepmind/deepmind/117.lean`), vs "Some of my new and almost
  new problems and results in combinatorial geometry"
  (`deepmind/deepmind/111.lean`); DEFERRED.)
-/

open scoped Topology

/--
Erdős Problem #68 [Er68d, Er88c (p.102), Er90, Er97e, Er97f] — OPEN:

Is the sum ∑_{n≥2} 1/(n! - 1) irrational?

Erdős [Er88c] notes that ∑ 1/(n! + t) should be transcendental for every integer t.
Weisenberg observed that this sum can also be written as ∑_{k≥1} ∑_{n≥2} 1/(n!)^k
(variant `erdos_problem_68.variants.weisenberg`). The decimal expansion of the sum
(≈ 1.2535) is OEIS A331373.

Encoding notes: the problem is an open yes/no question; following this corpus's
convention (no `answer()` macro with Mathlib-only imports), this theorem is the
direct assertion of the conjectured "yes" direction — irrationality — the direction
supported by Erdős's transcendence expectation recorded above (transcendence of
∑ 1/(n! + t) at t = -1 would imply this statement). The upstream formal-conjectures
file states the same sum's irrationality as the RHS of `answer(sorry) ↔ …`,
committing to no direction; its index shift `(n + 2).factorial` and this file's
`if n < 2` guard describe the same series term-for-term. The subtraction in
`(n.factorial - 1)` elaborates in ℝ (real subtraction of the cast), not truncated
ℕ subtraction; on the guarded indices n ≥ 2 the two would agree anyway. The
n = 0, 1 terms are set to 0 by the guard (and would be 0 regardless, since
1/(1 - 1) = 1/0 = 0 in Lean's ℝ), so the tsum is exactly ∑_{n≥2} 1/(n! - 1); the
series is summable (comparison with ∑ 2/n!), so `∑'` denotes the honest sum and the
irrationality claim is about the genuine real number, not a junk value.
-/
theorem erdos_problem_68 :
    Irrational (∑' (n : ℕ), if n < 2 then 0 else (1 : ℝ) / (n.factorial - 1)) :=
  sorry

/--
Page-confirmed variant (Weisenberg's observation, stated on the page without a
citation key): ∑_{n≥2} 1/(n! - 1) = ∑_{k≥1} ∑_{n≥2} 1/(n!)^k. Each n-term is a
geometric series — 1/(n! - 1) = ∑_{k≥1} (1/n!)^k for n! > 1 — and all terms are
nonnegative, so the summation order may be exchanged (Tonelli). The outer index
k : ℕ is shifted by one (`k + 1` ranges over the page's k ≥ 1), and the page's
k-outer, n-inner order is kept. The upstream formal-conjectures file proves the
n-outer form as `sum_factorial_inv_eq_geometric` (category `textbook`).

NOTE: this variant was added by the Fable review and is NOT compile-verified; it
uses only constructs already present in the file (tsum, the `if n < 2` guard, real
division and casts, ℕ-exponent powers on ℝ).
-/
theorem erdos_problem_68.variants.weisenberg :
    (∑' (n : ℕ), if n < 2 then 0 else (1 : ℝ) / (n.factorial - 1)) =
      ∑' (k : ℕ), ∑' (n : ℕ),
        if n < 2 then 0 else (1 : ℝ) / (n.factorial : ℝ) ^ (k + 1) := by
  sorry
