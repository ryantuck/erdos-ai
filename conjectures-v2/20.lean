import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

/-!
# Erdős Problem #20 — the Erdős–Rado sunflower conjecture

Verbatim statement from the source page: "Let $f(n,k)$ be minimal such that
every family $\mathcal{F}$ of $n$-uniform sets with
$\lvert\mathcal{F}\rvert \geq f(n,k)$ contains a $k$-sunflower. Is it true
that \[f(n,k) < c_k^n\] for some constant $c_k > 0$?"

Status: OPEN, $1000 prize — erdosproblems.com/20, page edition 25 January
2026, accessed 2026-03-05 (recovered from the originating pipeline session's
page capture); banner tooltip: "This is open, and cannot be resolved with a
finite computation." The teorth/erdosproblems metadata mirror agrees: state
"open" (last update 2025-08-31), prize $1000, comment "sunflower
conjecture", tags [combinatorics], OEIS A332077.

Known results (page remarks): Erdős and Rado [ErRa60] originally proved
f(n,k) ≤ (k-1)^n·n! (but see the encoding note on
`erdos_problem_20.variants.erdos_rado` below — under the page's own
≥-threshold definition of f the literal inequality fails at small
parameters, and the classical theorem is the strict-threshold form).
Kostochka [Ko97] improved this slightly (in particular establishing an
upper bound of o(n!), for which Erdős awarded him a $100 consolation
prize), but the bound stood at n^{(1+o(1))n} for a long time until Alweiss,
Lovett, Wu, and Zhang [ALWZ20] proved f(n,k) < (Ck·log n·log log n)^n for
some constant C > 1. This was refined slightly, independently by Rao
[Ra20], Frankston, Kahn, Narayanan, and Park [FKNP19], and Bell,
Chueluecha, and Warnke [BCW21], leading to the current record
f(n,k) < (Ck·log n)^n for some constant C > 1. The proof was streamlined by
Hu; a constant of C = 64 was achieved in a presentation by Stoeckl.

In [Er81] Erdős offered $1000 for a proof or disproof even just in the
special case k = 3, which he expected "contains the whole difficulty". He
also wrote "I really do not see why this question is so difficult".

The usual focus is the regime where k = O(1) is fixed (say k = 3) and n is
large; for the opposite regime Kostochka, Rödl, and Talysheva [KRT99]
showed f(n,k) = (1 + O_n(k^{-1/2^n}))·k^n (not formalized here: it needs
n-indexed asymptotic machinery not present in this file).

Encoding notes:
- The question is an open yes/no question; per this pipeline's convention
  for raw conjecture files (no `answer()` elaborator here) the theorems
  assert the conjectured ("yes") direction directly. The upstream
  google-deepmind/formal-conjectures file
  (`FormalConjectures/ErdosProblems/20.lean`, linked from the page) states
  the same content as `answer(sorry) ↔ ∃ c : ℕ → ℕ, ∀ n k, n > 0 →
  f n k < (c k)^n`, with f defined via `sInf`; the threshold form below is
  equivalent for n ≥ 1 (f(n,k) < c^n makes every family of size ≥ c^n
  contain a k-sunflower; conversely the threshold statement gives
  f(n,k) ≤ ⌈c^n⌉ < (3·max(c,1))^n, and the existential over c absorbs the
  constant change).
- The `1 ≤ n` hypothesis is essential, and matches the upstream `n > 0`
  restriction: at n = 0 we have c^0 = 1 for every real c, and the 0-uniform
  family F = {∅} has card 1 ≥ 1 but contains no k-sunflower for k ≥ 2, so
  the unrestricted statement is literally false. (The source's f(0,k) is
  undefined/infinite for k ≥ 2 — no threshold forces a k-sunflower among
  0-uniform sets — so the intended question is n ≥ 1.)
- Family and members are `Finset`s. This is faithful: the thresholds are
  finite, any infinite family contains a finite subfamily above the
  threshold, and a sunflower of a subfamily is one of the family; members
  are finite because they are n-element sets.

Related OEIS sequence: A332077. Tag: combinatorics. Additional thanks
(page): Alfaiz, Zachary Chase, Jake Mallen, and Desmond Weisenberg.

## References

Problem-source citation keys (page order): [Er65b], [Er69], [Er71, p.104],
[Er73], [Er81], [Er90], [Er95], [Er97c], [Er97d], [Va99, 3.63]. The
erdosproblems.com bibliography endpoint (`/latex/20`, `/bibs/`) was not
captured in the session logs, so entries below are honest stubs: those
marked (sibling-corpus) carry data attested consistently by other files of
this corpus that use the same key — flagged, not source-verified — and
conflicted or unattested keys stay key-only rather than fabricated.

- [Er65b] Erdős, P. (1965). [Key-only stub: the corpus carries two
  conflicting titles for this key — "Extremal problems in number theory"
  vs "Some recent advances and current problems in number theory" —
  unresolved.]
- [Er69] Erdős, P., _On some applications of graph theory to number
  theoretic problems_. Publ. Ramanujan Inst. 1 (1969), 131–136.
  (sibling-corpus)
- [Er71] Erdős, P. (1971). [Key-only stub: corpus conflict — "Some
  unsolved problems in graph theory and combinatorial analysis" vs "Topics
  in combinatorial analysis" — unresolved. The page cites p.104.]
- [Er73] Erdős, P., _Problems and results on combinatorial number theory_.
  A survey of combinatorial theory (Proc. Internat. Sympos., Colorado
  State Univ., Fort Collins, Colo., 1971) (1973), 117–138. (sibling-corpus)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like
  to see solved_. Combinatorica 1 (1981), 25–42. (sibling-corpus)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to
  Paul Erdős (1990), 467–478. (sibling-corpus; one corpus outlier assigns
  this key a different title — majority reading used, flagged)
- [Er95] Erdős, P. (1995). [Key-only stub: corpus carries conflicting
  data for this key.]
- [Er97c] Erdős, P. (1997). [Key-only stub: corpus conflict — "Some of my
  favorite problems and results" vs "Some recent problems and results in
  graph theory" — unresolved.]
- [Er97d] Erdős, P. (1997). [Key-only stub: corpus carries conflicting
  data for this key.]
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999). Cited here at 3.63. (sibling-corpus)

Remarks citation keys (author names source-verified from the page prose;
years per key suffix; no further bibliographic data recovered):
- [ErRa60] Erdős, P. and Rado, R. (1960). [Stub — the paper proving the
  original sunflower lemma bound.]
- [Ko97] Kostochka, A. (1997). [Stub — the o(n!) improvement.]
- [ALWZ20] Alweiss, R., Lovett, S., Wu, K., and Zhang, J. (2020). [Stub —
  the (Ck·log n·log log n)^n bound.]
- [Ra20] Rao, A. (2020). [Stub — refinement to (Ck·log n)^n.]
- [FKNP19] Frankston, K., Kahn, J., Narayanan, B., and Park, J. (2019).
  [Stub — independent refinement to (Ck·log n)^n.]
- [BCW21] Bell, T., Chueluecha, S., and Warnke, L. (2021). [Stub —
  independent refinement to (Ck·log n)^n.]
- [KRT99] Kostochka, A., Rödl, V., and Talysheva, L. (1999). [Stub — the
  large-k regime asymptotic.]
-/

/--
A family `F` of finite sets is **n-uniform** if every member has cardinality `n`.
-/
def NUniform {α : Type*} (F : Finset (Finset α)) (n : ℕ) : Prop :=
  ∀ S ∈ F, Finset.card S = n

/--
A **k-sunflower** (or Δ-system of size k) in a family of sets is a subfamily
of `k` sets such that every pair shares the same intersection (the "core").
Equivalently, there exists a core `C` such that for any two distinct members
`S₁, S₂` of the subfamily, `S₁ ∩ S₂ = C`.

Degenerate cases: for `k ≤ 1` the pairwise condition is vacuous, so any
subfamily of the right cardinality is a `k`-sunflower — the standard
convention, matching the upstream formal-conjectures `IsSunflower` (which
proves the empty and singleton cases as `test` lemmas).
-/
def IsSunflower {α : Type*} [DecidableEq α] (G : Finset (Finset α)) (k : ℕ) : Prop :=
  Finset.card G = k ∧
    ∃ C : Finset α, ∀ S₁ ∈ G, ∀ S₂ ∈ G, S₁ ≠ S₂ → S₁ ∩ S₂ = C

/--
Erdős Problem #20 [Er65b, Er69, Er71 (p.104), Er73, Er81, Er90, Er95,
Er97c, Er97d, Va99 (3.63)]:

Let f(n,k) be minimal such that every family F of n-uniform sets with
|F| ≥ f(n,k) contains a k-sunflower. Is it true that f(n,k) < c_k^n
for some constant c_k > 0?

This is the sunflower conjecture of Erdős and Rado. It is an OPEN yes/no
question ($1000 prize); the statement below asserts the conjectured ("yes")
direction, in threshold form: for every k ≥ 1 there is a constant c > 0
such that every n-uniform family (n ≥ 1) of size at least c^n contains a
k-sunflower. The `1 ≤ n` hypothesis is required — without it the statement
is falsified by the 0-uniform family {∅} (see the module docstring).

Erdős and Rado [ErRa60] proved f(n,k) ≤ (k-1)^n·n!; Kostochka [Ko97]
improved this to o(n!). Alweiss, Lovett, Wu, and Zhang [ALWZ20] proved
f(n,k) < (Ck·log n·log log n)^n for some constant C > 1, and independent
refinements by Rao [Ra20], Frankston–Kahn–Narayanan–Park [FKNP19], and
Bell–Chueluecha–Warnke [BCW21] give the current record
f(n,k) < (Ck·log n)^n. In [Er81] Erdős offered $1000 for a proof or
disproof even in the case k = 3.
-/
theorem erdos_problem_20 :
    ∀ k : ℕ, 1 ≤ k →
      ∃ c : ℝ, 0 < c ∧
        ∀ (α : Type*) [DecidableEq α] (n : ℕ) (F : Finset (Finset α)),
          1 ≤ n →
          NUniform F n →
          (Finset.card F : ℝ) ≥ c ^ n →
          ∃ G : Finset (Finset α), G ⊆ F ∧ IsSunflower G k :=
  sorry

/--
Erdős Problem #20, variant (solved) — the Erdős–Rado sunflower lemma
[ErRa60]: every n-uniform family with more than (k-1)^n·n! members contains
a k-sunflower.

Encoding note (page-stated bound corrected): the page's remark states
"f(n,k) ≤ (k-1)^n·n!", which under the page's own ≥-threshold definition of
f is literally false at small parameters — e.g. (n,k) = (1,2): a family of
one singleton has |F| = 1 ≥ 1 = (2-1)^1·1! but contains no 2-sunflower, so
f(1,2) = 2 > 1. The classical Erdős–Rado theorem is the strict-threshold
form |F| > n!·(k-1)^n stated here (equivalently f(n,k) ≤ (k-1)^n·n! + 1),
which is tight at n = 1 (f(1,k) = k = 1!·(k-1)^1 + 1). No `1 ≤ n`
hypothesis is needed: at n = 0 the hypothesis card F > 1 is unsatisfiable
for 0-uniform families (F ⊆ {∅}), and the ℕ-truncated `k - 1` is exact
under `1 ≤ k` (and harmless anyway at k = 0).

Not compile-verified (statement added by the fable-review pipeline; uses
`Nat.factorial` from an added import).
-/
theorem erdos_problem_20.variants.erdos_rado :
    ∀ k : ℕ, 1 ≤ k →
      ∀ (α : Type*) [DecidableEq α] (n : ℕ) (F : Finset (Finset α)),
        NUniform F n →
        (k - 1) ^ n * Nat.factorial n < Finset.card F →
        ∃ G : Finset (Finset α), G ⊆ F ∧ IsSunflower G k :=
  sorry

/--
Erdős Problem #20, variant (open) — the k = 3 special case, for which
[Er81] offers the $1000 prize ("even just in the special case when k = 3,
which he expected 'contains the whole difficulty'"): there is a constant
c > 0 such that every n-uniform family (n ≥ 1) with at least c^n members
contains a 3-sunflower. Asserted in the conjectured ("yes") direction, as
in the main statement.

Not compile-verified (statement added by the fable-review pipeline).
-/
theorem erdos_problem_20.variants.k_eq_three :
    ∃ c : ℝ, 0 < c ∧
      ∀ (α : Type*) [DecidableEq α] (n : ℕ) (F : Finset (Finset α)),
        1 ≤ n →
        NUniform F n →
        (Finset.card F : ℝ) ≥ c ^ n →
        ∃ G : Finset (Finset α), G ⊆ F ∧ IsSunflower G 3 :=
  sorry

/--
Erdős Problem #20, variant (solved) — the current record bound
f(n,k) < (Ck·log n)^n for some constant C > 1, obtained independently by
Rao [Ra20], Frankston–Kahn–Narayanan–Park [FKNP19], and
Bell–Chueluecha–Warnke [BCW21], refining Alweiss–Lovett–Wu–Zhang [ALWZ20]
(who proved the bound with an extra log log n factor).

Encoding note: the page displays the bound without restricting n, but at
n = 1 it is literally false for every C (log 1 = 0 while f(1,k) = k ≥ 2 for
k ≥ 2), so the statement here carries the reviewer's `2 ≤ n` guard; for
n ≥ 2, log n > 0 and the threshold form below (families of size at least
(Ck·log n)^n contain a k-sunflower) follows from f(n,k) < (Ck·log n)^n as
in the main statement's encoding note.

Not compile-verified (statement added by the fable-review pipeline; uses
`Real.log` from an added import).
-/
theorem erdos_problem_20.variants.record_bound :
    ∃ C : ℝ, 1 < C ∧
      ∀ k : ℕ, 1 ≤ k →
        ∀ (α : Type*) [DecidableEq α] (n : ℕ) (F : Finset (Finset α)),
          2 ≤ n →
          NUniform F n →
          (Finset.card F : ℝ) ≥ (C * (k : ℝ) * Real.log (n : ℝ)) ^ n →
          ∃ G : Finset (Finset α), G ⊆ F ∧ IsSunflower G k :=
  sorry
