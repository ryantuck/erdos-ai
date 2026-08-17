import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem 71

*Reference:* [erdosproblems.com/71](https://www.erdosproblems.com/71)
(accessed 2026-02-22; page content recovered from two archived captures in the
original pipeline session's log,
`claude-session-logs/56264107-bf57-4538-bc54-ec92f1241751.jsonl` — line 7, a Read
of the then-extant `html/71.html` (full 26 KB page), and line 11, a Read of
`tidy/71.html` (the problem-box div); the two captures agree on statement,
status banner, citations, tags, and remarks. The live site is unreachable from
the review container.)

Statement (verbatim from the site): "Is it true that for every infinite
arithmetic progression $P$ which contains even numbers there is some constant
$c=c(P)$ such that every graph with average degree at least $c$ contains a
cycle whose length is in $P$?" Cited on the page as [Er82e][Er95][Er97b].
Tags: graph theory | cycles. No prize; no OEIS reference.

Status: **PROVED** (tooltip: "This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) records the current status as **proved (Lean)** (last update
2026-06-07): the affirmative resolution has since been *formally verified in
Lean*. The upstream google-deepmind/formal-conjectures repository (HEAD
dd1c2beb, fetched 2026-08-16) has `ErdosProblems/71.lean` stating the same
proposition in question form (`answer(True) ↔ …`, category `research solved`)
with a `formal_proof` attribute pointing at
<https://github.com/Jayyhk/erdos-lean/blob/110d489e/problems/71/Erdos71.lean>.
The page captures predate this (at capture time the page still said
"Formalised statement? No").

Remarks from the page: "In [Er82e] Erdős credits this conjecture to himself and
Burr. This has been proved by Bollobás [Bo77]. The best dependence of the
constant $c(P)$ is unknown. See also [72]." (Problem #72 — same tags, $100,
also proved — asks the density-zero analogue of the same
average-degree-forces-a-cycle phenomenon.)

References (per-entry provenance; the `/latex/71` payload survives in the logs
only as a WebFetch summary, so entries rest on that summary, the upstream
formal-conjectures file, and corpus consensus — nothing is fabricated):

- [Bo77] Bollobás, B., _Cycles modulo k_. Bull. London Math. Soc. 9 (1977),
  97-98. (Journal/year/pages from the `/latex/71` capture and upstream
  formal-conjectures; volume 9 from the original pipeline file and prior
  review, corroborated by `deepmind/deepmind/72.lean`.)
- [Er82e] Erdős, P., _Some of my favourite problems which recently have been
  solved_. (1982), 59-79. (Title/year/pages from the `/latex/71` capture,
  agreeing with upstream formal-conjectures; the venue was not captured —
  DEFERRED. Note: the archived styled copy `deepmind/deepmind/71.lean` expands
  this key differently ("Problems and results on finite and infinite
  combinatorial analysis II", L'Enseignement Math. 27); that expansion
  contradicts both the `/latex/71` capture and upstream and is not used here.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Upstream
  formal-conjectures `ErdosProblems/71.lean`; volume-level data DEFERRED.)
- [Er97b] Erdős, P., _Some old and new problems in various branches of
  combinatorics_. Discrete Math. (1997), 227-231. (Upstream formal-conjectures
  `ErdosProblems/71.lean`; volume-level data DEFERRED.)
-/

open SimpleGraph

/--
Erdős Problem #71 [Er82e, Er95, Er97b] — PROVED (and since verified in Lean):

Is it true that for every infinite arithmetic progression P which contains even
numbers there is some constant c = c(P) such that every graph with average
degree at least c contains a cycle whose length is in P?

In [Er82e] Erdős credits this conjecture to himself and Burr. It was proved by
Bollobás [Bo77], so the answer is yes. (This is *not* the well-known
"Burr–Erdős conjecture" on Ramsey numbers of bounded-degeneracy graphs, proved
by Lee; the page never uses that name.) The best dependence of the constant
c(P) is unknown. See also Problem #72.

Encoding notes: the problem is a yes/no question resolved affirmatively;
following this corpus's convention (no `answer()` macro with Mathlib-only
imports), this theorem is the direct assertion of the *true* direction, so the
polarity matches the resolution. The infinite AP is parametrized as
P = {a + k·d : k ∈ ℕ} with d ≥ 1 (infinitude is then automatic), "contains
even numbers" as `∃ k, Even (a + k * d)`, and the average degree of a graph on
n > 0 vertices as 2|E(G)|/n computed in ℝ, guarded by `0 < Fintype.card V`.
Strengthening the existence to `c > 0` is harmless (any witness may be
replaced by `max c 1`). Mathlib's `Walk.IsCycle` forces cycle length ≥ 3, so
degenerate small elements of P (0, 1, 2) cannot be spuriously witnessed.
-/
theorem erdos_problem_71 (a d : ℕ) (hd : 1 ≤ d) (heven : ∃ k : ℕ, Even (a + k * d)) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        0 < Fintype.card V →
        c ≤ (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card V : ℝ) →
        ∃ m : ℕ, (∃ k : ℕ, m = a + k * d) ∧
          ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m :=
  sorry
