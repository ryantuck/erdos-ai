import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic

/-!
# Erdős Problem 66

*Reference:* [erdosproblems.com/66](https://www.erdosproblems.com/66)
(accessed 2026-03-05; page edition "last edited 23 January 2026"; page content
recovered from two byte-agreeing archived captures in the original pipeline session's
log, `claude-session-logs/2c281092-3c7a-43d1-933d-fa6e7af0789c.jsonl` line 12 — the
live site is unreachable from the review container).

Statement (verbatim from the site): "Is there $A\subseteq \mathbb{N}$ such that
$$\lim_{n\to \infty}\frac{1_A\ast 1_A(n)}{\log n}$$ exists and is $\neq 0$?"
Cited on the page as [Er56][Er59][ErGr80][Er85c][Er89d][Er90][Er95][Er97c][Er97f]
[Va99,1.16]. Tags: number theory | additive basis. Prize: **$500**. No OEIS entry
(mirror lists "N/A").

Status: **OPEN** (tooltip: "This is open, and cannot be resolved with a finite
computation."). The teorth/erdosproblems metadata mirror (`data/problems.yaml`,
commit a09c7a2, 2026-08-14) agrees: open, last update 2025-08-31, prize $500. The
upstream google-deepmind/formal-conjectures repository (checked at HEADs 273e79a and
dd1c2be, both fetched 2026-08-16) has `ErdosProblems/66.lean` with
`@[category research open]` and `answer(sorry)`, matching the page's
"Formalised statement? Yes" link.

Remarks from the page: "A suitably constructed random set has this property if we are
allowed to ignore an exceptional set of density zero. The challenge is obtaining this
with no exceptional set. Erdős believed the answer should be no. Erdős and Sárközy
proved that $$\frac{\lvert 1_A\ast 1_A(n)-\log n\rvert}{\sqrt{\log n}}\to 0$$ is
impossible. Erdős suggests it may even be true that the $\liminf$ and $\limsup$ of
$1_A\ast 1_A(n)/\log n$ are always separated by some absolute constant." Horváth
[Ho07] proved that $$\lvert 1_A\ast 1_A(n)-\log n\rvert \leq (1-\epsilon)\sqrt{\log n}$$
cannot hold for all large $n$. Additional thanks (per the page): Boris Alexeev and
Mark Sellke. 1 comment on the problem (content not captured).

The Erdős–Sárközy and Horváth results are formalized as variants below. The
liminf/limsup-separation suggestion is deliberately left as prose: it is only a
suggestion ("may even be true"), and a faithful `Filter.limsup` encoding over ℝ would
need an explicit boundedness guard (for $A$ with unbounded ratio, `Real` `sSup` junk
values could silently distort the statement — the problem-33 failure class in this
corpus), which would require constructs not otherwise in this file.

References (per-entry provenance; the page's `/latex/66` and `/bibs/` payloads were
NOT captured in the logs, so journal/volume data below is corpus-consensus, marked
DEFERRED — nothing is fabricated):

- [Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la
  Théorie des Nombres, Bruxelles, 1955 (1956), 127-137. (Corpus-consensus entry, e.g.
  `conjectures-v2/31.lean`, `conjectures-v2/32.lean`; DEFERRED.)
- [Er59] Erdős, P., _Über einige Probleme der additiven Zahlentheorie_. Sammelband zu
  Ehren des 250. Geburtstages Leonhard Eulers (1959), 116-119. (Corpus-consensus
  entry; DEFERRED.)
- [ErGr80] Erdős, P. and Graham, R.L., _Old and new problems and results in
  combinatorial number theory_. Monographies de L'Enseignement Mathématique 28
  (1980). (Corpus-consensus entry; DEFERRED.)
- [Er85c] Erdős, P., _On some of my problems in number theory I would most like to
  see solved_. Number theory (Ootacamund, 1984) (1985), 74-84. (Corpus-majority
  entry; a minority of sibling files record a title disagreement for this key;
  DEFERRED.)
- [Er89d] Erdős, P. (1989). (Key-only stub: one sibling expands as "On some of my
  problems in number theory" without venue data, and the log-recovered `/latex/29`
  extraction for the same key had no entry; DEFERRED.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
  Erdős (1990), 467-478. (Corpus-consensus entry; DEFERRED.)
- [Er95] Erdős, P. (1995). (Key-only stub: the corpus carries two conflicting
  expansions — "Some of my favourite problems in various branches of combinatorics",
  Combinatorics '94 (Catania), Congressus Numerantium 107 (1995), and "Some of my
  favourite problems in number theory, combinatorics, and geometry", Resenhas 1
  (1995), 165-186 — and the page gives no page-pointer for #66 to disambiguate;
  DEFERRED.)
- [Er97c] Erdős, P. (1997). (Key-only stub: sibling corpus expansions conflict —
  "Some recent problems and results in graph theory", Discrete Math. 164 (1997),
  81-85, vs "Some of my favorite problems and results"; DEFERRED.)
- [Er97f] Erdős, P. (1997). (Key-only stub: sibling corpus expansions conflict —
  "Some unsolved problems", Combinatorics, geometry and probability (Cambridge,
  1993) (1997), 1-10, among others; DEFERRED.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the
  conference "Paul Erdős and his mathematics", Budapest, July 1999 (1999). The page
  cites this problem as [Va99, 1.16]. (Corpus-majority reading of this key — a
  minority of sibling files expand it as works of Vardi, I.; DEFERRED.)
- [Ho07] Horváth (2007). (Key-only stub from the page's remarks; no expansion of
  this key is recoverable offline; DEFERRED.)
- The page attaches no citation key to the Erdős–Sárközy impossibility result
  (reviewer note: it belongs to the Erdős–Sárközy series "Problems and results on
  additive properties of general sequences"; precise details DEFERRED).
-/

open Filter

/--
The additive representation count: the number of ordered pairs (a, b) ∈ A × A
with a + b = n. Equivalently, (1_A ∗ 1_A)(n).

Encoding note: the counted set {a | a ∈ A ∧ a ≤ n ∧ (n - a) ∈ A} is in bijection
with the ordered pairs (a, n - a); the guard `a ≤ n` is required because ℕ
subtraction truncates (without it, every a > n with 0 ∈ A would be spuriously
counted). The set is contained in {0, …, n}, hence finite, so `Set.ncard` is the
honest cardinality (no infinite-set junk value). This definition agrees with
`sumRep` in the upstream google-deepmind/formal-conjectures repository
(`FormalConjecturesForMathlib/Combinatorics/Additive/Convolution.lean`), which
counts the pairs on `Finset.antidiagonal n`. Small-case checks: A = {1,2}, n = 3
gives 2 (pairs (1,2),(2,1)); A = {1}, n = 2 gives 1 (pair (1,1)); n = 0 gives 1
iff 0 ∈ A (pair (0,0)).
-/
noncomputable def repCount (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {a : ℕ | a ∈ A ∧ a ≤ n ∧ (n - a) ∈ A}

/--
Erdős Problem #66 [Er56, Er59, ErGr80, Er85c, Er89d, Er90, Er95, Er97c, Er97f,
Va99 (1.16)] — OPEN, $500 prize:

Is there A ⊆ ℕ such that lim_{n → ∞} (1_A ∗ 1_A)(n) / log n exists and is ≠ 0?

Erdős believed the answer should be no; this theorem is the direct assertion of that
believed (negative) direction, following this corpus's convention for open yes/no
questions. (The upstream formal-conjectures file states the same proposition as the
RHS of `answer(sorry) ↔ ∃ A c, c ≠ 0 ∧ Tendsto …`, committing to no direction; the
existential body here matches it term-for-term.) A suitably constructed random set
has this property if we allow an exceptional set of density zero, but the challenge
is obtaining this with no exceptional set. Erdős and Sárközy proved that
|1_A ∗ 1_A(n) − log n| / √(log n) → 0 is impossible (variant
`erdos_problem_66.variants.erdos_sarkozy`), which Horváth [Ho07] strengthened
(variant `erdos_problem_66.variants.horvath`). Erdős suggested it may even be true
that the liminf and limsup of 1_A ∗ 1_A(n)/log n are always separated by an absolute
constant (not formalized; see the module docstring).

Encoding notes: "the limit exists and is ≠ 0" is rendered as
`∃ L ≠ 0, Tendsto … (nhds L)` — existence of a *finite* nonzero limit, the standard
reading (and upstream's); a set with ratio → ∞ (e.g. A = ℕ) is not a witness. At
n = 0 and n = 1 the quotient is Lean-junk (`Real.log ≤ 0`, division by zero gives
0); this is harmless under `atTop`. Since repCount ≥ 0 and log n > 0 eventually,
any limit L is automatically ≥ 0.
-/
theorem erdos_problem_66 :
    ¬ ∃ (A : Set ℕ) (L : ℝ),
      L ≠ 0 ∧ Tendsto (fun n : ℕ => (repCount A n : ℝ) / Real.log (n : ℝ)) atTop (nhds L) :=
  sorry

/--
Page-confirmed variant (SOLVED): "Erdős and Sárközy proved that
|1_A ∗ 1_A(n) − log n| / √(log n) → 0 is impossible" — i.e. for every A ⊆ ℕ the
displayed ratio does not tend to 0. The page attaches no citation key to this result
(see the module docstring). At n ∈ {0, 1} the quotient is Lean-junk (√(log n) = 0,
division by zero gives 0), harmless under `atTop`. The binder `A` before the colon is
ordinary universal quantification, as intended for this direct assertion.

NOTE: this variant was added by the Fable review and is NOT compile-verified. Its
`Real.sqrt` relies on the added `Mathlib.Data.Real.Sqrt` import, which coexists with
this file's other imports in the compile-verified sibling `conjectures/1024.lean`.
-/
theorem erdos_problem_66.variants.erdos_sarkozy (A : Set ℕ) :
    ¬ Tendsto
        (fun n : ℕ =>
          |(repCount A n : ℝ) - Real.log (n : ℝ)| / Real.sqrt (Real.log (n : ℝ)))
        atTop (nhds 0) :=
  sorry

/--
Page-confirmed variant (SOLVED): "Horváth [Ho07] proved that
|1_A ∗ 1_A(n) − log n| ≤ (1 − ε)√(log n) cannot hold for all large n" — i.e. for
every A ⊆ ℕ and every fixed ε ∈ (0, 1), the bound fails for infinitely many n. This
quantitatively strengthens `erdos_problem_66.variants.erdos_sarkozy`: if the ratio
tended to 0 the bound would eventually hold for any such ε. The hypothesis ε < 1
restricts to the meaningful range (for ε ≥ 1 the right-hand side is ≤ 0 and the
impossibility is essentially degenerate); ε is universally quantified per instance —
there is no `∃`-constant that could absorb it.

NOTE: this variant was added by the Fable review and is NOT compile-verified (see
the import note on `erdos_problem_66.variants.erdos_sarkozy`).
-/
theorem erdos_problem_66.variants.horvath (A : Set ℕ) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε < 1) :
    ¬ ∀ᶠ n : ℕ in atTop,
        |(repCount A n : ℝ) - Real.log (n : ℝ)| ≤ (1 - ε) * Real.sqrt (Real.log (n : ℝ)) :=
  sorry
