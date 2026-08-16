import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Erdős Problem 67 — The Erdős Discrepancy Problem

*Reference:* [erdosproblems.com/67](https://www.erdosproblems.com/67)
(accessed 2026-03-05; page edition "last edited 23 January 2026"; page content
recovered from two agreeing archived captures in the original pipeline session's
log, `claude-session-logs/16976623-0532-4bcb-a9c0-d9a82a414890.jsonl` lines 10 and
16 — the live site is unreachable from the review container).

Statement (verbatim from the site): "If $f:\mathbb{N}\to \{-1,+1\}$ then is it true
that for every $C>0$ there exist $d,m\geq 1$ such that
$$\left\lvert \sum_{1\leq k\leq m}f(kd)\right\rvert > C?$$"

Cited on the page as [Er57][Er61][Er64b][Er65b][Er73][Er75b][ErGr79][ErGr80][Er81]
[Er82e][Er85c][Er90][Er97c][Va99,1.30]. Tag: discrepancy. Prize: **$500**.
Related OEIS sequences: A181740, A237695.

Status: **PROVED** (banner tooltip: "This has been solved in the affirmative.").
Page remarks: "The Erdős discrepancy problem. This is true, and was proved by Tao
[Ta16], who also proved the more general case when $f$ takes values on the unit
sphere. In several places (e.g. [Er64b], [Er65b], and [Er81]) Erdős further
conjectured that $$\max_{md\leq x}\left\lvert \sum_{1\leq k\leq m}f(kd)\right\rvert
\gg \log x.$$ In [Er85c] Erdős also asks about the special case when $f$ is
multiplicative." The two remarks are formalized as variants below.

The teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) agrees with the banner: proved, last update 2025-08-31, prize $500,
comment "Erdős discrepancy problem". The upstream google-deepmind/formal-conjectures
repository (HEAD dd1c2be, fetched 2026-08-16, byte-identical to the pipeline log's
earlier capture apart from an import rename) has
`FormalConjectures/ErdosProblems/67.lean` with `@[category research solved]`, the
same statement over `Finset.Icc 1 m`, and a complex unit-sphere variant
(`erdos_67.variants.complex`) — matching the page's "Formalised statement? Yes".
The unit-sphere generalization is deliberately NOT duplicated here: it needs
`Metric.sphere (0 : ℂ) 1` and norm machinery far outside this file's imports, and
it is already formalized upstream.

References (per-entry provenance; no `/latex/67` or `/bibs/` payload was captured
in any session log, so entries below come from the upstream formal-conjectures
reference block and from sibling corpus files, and are marked DEFERRED where
incomplete or conflicting — nothing is fabricated):

- [Ta16] Tao, Terence, _The Erdős discrepancy problem_. Discrete Analysis (2016),
  Paper No. 1, 29 pp. (Recovered verbatim from the upstream formal-conjectures
  `ErdosProblems/67.lean` reference block.)
- [Er57] Erdős, P., _Some unsolved problems_ (1957). (Corpus-consensus stub, e.g.
  `deepmind/deepmind/222.lean`; venue data DEFERRED.)
- [Er61] Erdős, P., _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int.
  Közl. 6 (1961), 221-254. (Corpus-consensus entry; DEFERRED.)
- [Er64b] Erdős, P. (1964). (Key-only stub: sibling corpus files conflict —
  _Problems and results on diophantine approximations_, Compositio Math. 16 (1964),
  52-65, vs _Some problems in number theory_; DEFERRED.)
- [Er65b] Erdős, P. (1965). Lectures on Modern Mathematics III (1965), 196-244.
  (Sibling files agree on the venue but disagree on the title; DEFERRED.)
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey
  of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort
  Collins, 1971) (1973), 117-138. (Corpus-consensus entry; DEFERRED.)
- [Er75b] Erdős, P. (1975). (Key-only stub: sibling files disagree on this key;
  DEFERRED.)
- [ErGr79] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_ (1979). (Sibling files disagree on the venue;
  DEFERRED.)
- [ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique 28
  (1980). (Corpus-consensus entry; DEFERRED.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to see
  solved_. Combinatorica 1 (1981), 25-42. (Corpus-consensus entry, matching the
  log-recovered `/latex/19` fetch for the same key; DEFERRED.)
- [Er82e] Erdős, P. (1982). (Key-only stub: sibling files disagree on the title;
  one candidate venue is L'Enseignement Math. 27 (1982), 163-176; DEFERRED.)
- [Er85c] Erdős, P., _On some of my problems in number theory I would most like to
  see solved_. Number theory (Ootacamund, 1984) (1985), 74-84. (Corpus-majority
  entry; DEFERRED.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
  Erdős (1990), 467-478. (Corpus-consensus entry; DEFERRED.)
- [Er97c] Erdős, P. (1997). (Key-only stub: sibling corpus expansions conflict —
  _Some recent problems and results in graph theory_, Discrete Math. 164 (1997),
  81-85, vs _Some of my favorite problems and results_; DEFERRED.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999). The page
  cites this problem as [Va99, 1.30]. (Corpus-majority reading of this key;
  DEFERRED.)
-/

open BigOperators Finset

/--
Erdős Problem #67 — The Erdős Discrepancy Problem
[Er57, Er61, Er64b, Er65b, Er73, Er75b, ErGr79, ErGr80, Er81, Er82e, Er85c, Er90,
Er97c, Va99 (1.30)] — PROVED, $500 prize:

If f : ℕ → {-1, +1} then is it true that for every C > 0 there exist d, m ≥ 1 such
that |∑_{1 ≤ k ≤ m} f(k * d)| > C?

This is true: proved by Tao [Ta16], who also proved the more general case when f
takes values on the unit sphere (formalized upstream as `erdos_67.variants.complex`;
see the module docstring). Following this corpus's convention, the affirmatively
solved yes/no question is stated as a direct assertion of the true direction.

Encoding notes:
- `∑ k ∈ range m, f ((k + 1) * d)` runs over f(d), f(2d), …, f(m*d) — exactly
  ∑_{1 ≤ k ≤ m} f(k*d); the 0-indexed shift is term-by-term exact, and with
  0 < m the sum is never empty.
- The source's real threshold C > 0 is rendered as C : ℕ (ranging over all
  naturals, including 0). The two are equivalent because the sum is an integer:
  for real C > 0, apply the statement to ⌈C⌉ ≥ C; the C = 0 instance is simply
  weaker than the C = 1 instance.
- The hypothesis hf also constrains f 0 = ±1. This is harmless: f 0 occurs in no
  sum (the arguments (k+1)*d are ≥ 1), and every ±1-valued function on the
  positive integers extends to ℕ by setting f 0 = 1.
-/
theorem erdos_problem_67
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1)
    (C : ℕ) :
    ∃ d : ℕ, 0 < d ∧ ∃ m : ℕ, 0 < m ∧
      C < |∑ k ∈ range m, f ((k + 1) * d)| :=
  sorry

/--
Page-confirmed variant ([Er85c]; SOLVED): "In [Er85c] Erdős also asks about the
special case when f is multiplicative."

For a completely multiplicative sign function (f(a*b) = f(a)*f(b) for positive
a, b — the standard reading of "multiplicative" in the discrepancy-problem
literature), the general sum collapses: ∑_{1 ≤ k ≤ m} f(k*d) = f(d) * ∑_{1 ≤ k ≤ m}
f(k), so |∑_{1 ≤ k ≤ m} f(k*d)| = |∑_{1 ≤ k ≤ m} f(k)| and unbounded discrepancy is
equivalent to the d = 1 case: unbounded partial sums, the form stated here.
(Stating the (d, m)-form with the multiplicativity hypothesis verbatim would be a
trivially weaker corollary of `erdos_problem_67`; this collapsed form is the
substantive content.) True by Tao's theorem [Ta16] via the collapse identity.

Encoding note: the multiplicativity hypothesis is deliberately restricted to
0 < a and 0 < b. Extending it to a = 0 would, together with hf, force f ≡ 1
(f 0 = f 0 * f b and f 0 = ±1 ≠ 0 give f b = 1 for every b), collapsing the
statement to a claim about a single degenerate function.

NOTE: this variant was added by the Fable review pipeline and is NOT
compile-verified.
-/
theorem erdos_problem_67.variants.multiplicative
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1)
    (hmul : ∀ a b : ℕ, 0 < a → 0 < b → f (a * b) = f a * f b)
    (C : ℕ) :
    ∃ m : ℕ, 0 < m ∧ C < |∑ k ∈ range m, f (k + 1)| :=
  sorry

/--
Page-confirmed variant ([Er64b], [Er65b], [Er81]; OPEN): "In several places
(e.g. [Er64b], [Er65b], and [Er81]) Erdős further conjectured that
max_{m*d ≤ x} |∑_{1 ≤ k ≤ m} f(k*d)| ≫ log x."

This is a direct assertion of Erdős's conjectured strengthening (still open; Tao's
theorem gives unboundedness but no growth rate).

Encoding notes:
- "max_{m*d ≤ x} |·| ≥ c * log x" is rendered existentially: there are d, m ≥ 1
  with m * d ≤ x and c * log x ≤ |∑_{1 ≤ k ≤ m} f((k+1)*d)|.
- The implied constant c is quantified after f and before x: it may depend on f
  but must be uniform in x. (The ∃/∀ order is deliberate — placing ∃ c inside
  ∀ x would let c absorb the x-dependence and trivialize the bound.)
- "≫ log x" is asserted for all x ≥ 2 rather than "for all sufficiently large x";
  the two are equivalent up to shrinking c, since taking m = d = 1 shows the max
  is always ≥ |f(1)| = 1, so on any finite range 2 ≤ x ≤ x₀ the bound holds with
  any c ≤ 1 / log x₀.
- x ranges over ℕ, WLOG, since the constraint m * d ≤ x is integral and
  log is monotone.

NOTE: this variant (and the `Mathlib.Analysis.SpecialFunctions.Log.Basic` import
supporting `Real.log`) was added by the Fable review pipeline and is NOT
compile-verified; that import coexists with `Mathlib.Data.Real.Basic` in the
compile-verified sibling `conjectures/66.lean`.
-/
theorem erdos_problem_67.variants.log_discrepancy
    (f : ℕ → ℤ)
    (hf : ∀ n : ℕ, f n = 1 ∨ f n = -1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℕ, 2 ≤ x →
      ∃ d : ℕ, 0 < d ∧ ∃ m : ℕ, 0 < m ∧ m * d ≤ x ∧
        c * Real.log (x : ℝ) ≤ ((|∑ k ∈ range m, f ((k + 1) * d)| : ℤ) : ℝ) :=
  sorry
