import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# Erdős Problem 72

*Reference:* [erdosproblems.com/72](https://www.erdosproblems.com/72)
(accessed 2026-02-22; page content recovered from two archived captures in the
review-session log `claude-session-logs/41f5c3b4-57ea-424b-bf2f-90bb86af766f.jsonl`
— line 7, a Read of the then-extant `html/72.html` (full ~33 KB page), and
line 11, a Read of the then-extant `tidy/72.html` (the problem-box div); the two
captures agree on statement, status banner, prize, citations, tags, and remarks.
A third, independent WebFetch summary of the live page in the original pipeline
session log `a8e4b57d-…jsonl` line 13 confirms the verbatim question phrasing.
The live site is unreachable from the review container.)

Statement (verbatim from the site): "Is there a set $A\subset \mathbb{N}$ of
density $0$ and a constant $c>0$ such that every graph on sufficiently many
vertices with average degree $\geq c$ contains a cycle whose length is in $A$?"
Cited on the page as [Er94b][Er95][Er97b][Er97c]. Prize: \$100.
Tags: graph theory | cycles. No OEIS reference.

Status: **PROVED** (tooltip: "This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2,
2026-08-14) confirms: status "proved" (last update 2025-08-31), prize \$100,
tags graph theory/cycles, formalized "no". The upstream
google-deepmind/formal-conjectures repository (HEAD dd1c2beb, checked
2026-08-16) has no `ErdosProblems/72.lean`, consistent with the mirror's
"unformalized" state.

Remarks from the page: Bollobás [Bo77] proved that such a $c$ does exist if $A$
is an infinite arithmetic progression containing even numbers (see Problem #71).
Erdős was 'almost certain' that if $A$ is the set of powers of $2$ then no such
$c$ exists (although he conjectured that $n$ vertices and average degree
$\gg (\log n)^{C}$ suffices for some $C=O(1)$). If $A$ is the set of squares
(or the set of $p\pm 1$ for $p$ prime) then he had no guess. Solved by
Verstraëte [Ve05], who gave a non-constructive proof that such a set $A$
exists. Liu and Montgomery [LiMo20] proved that in fact this is true when $A$
is the set of powers of $2$ (more generally any set of even numbers which
doesn't grow too quickly) — in particular this contradicts the previous belief
of Erdős. The page also links the entry in the (UCSD) graphs problem
collection. Additional thanks: Richard Montgomery.

References (per-entry provenance; the `/latex/72` payload survives in the logs
only as a WebFetch summary — fc-session log `7228d698-…jsonl` line 19 — so
entries rest on that summary, upstream formal-conjectures files sharing the
same site-wide keys, and corpus corroboration; volume-level gaps are marked
DEFERRED, nothing is fabricated):

- [Er94b] Erdős, P., _Some problems in number theory, combinatorics and
  combinatorial geometry_. Math. Pannon. (1994), 261-269. (Expansion from
  upstream formal-conjectures `ErdosProblems/750.lean`/`98.lean` (MR1304854);
  volume DEFERRED.)
- [Er95] Erdős, P., _Some of my favourite problems in number theory,
  combinatorics, and geometry_. Resenhas (1995), 165-186. (Upstream
  `ErdosProblems/71.lean`; volume DEFERRED.)
- [Er97b] Erdős, P., _Some old and new problems in various branches of
  combinatorics_. Discrete Math. (1997), 227-231. (Upstream
  `ErdosProblems/71.lean`; volume DEFERRED.)
- [Er97c] Erdős, P., _Some of my favorite problems and results_. The
  mathematics of Paul Erdős, I (1997), 47-67. (Upstream
  `ErdosProblems/5.lean`/`47.lean`/`94.lean`.)
- [Bo77] Bollobás, B., _Cycles modulo k_. Bull. London Math. Soc. 9 (1977),
  97-98. (Journal/year/pages from the `/latex/72` capture; volume 9
  corroborated by the `/latex/71`-derived entry in `conjectures-v2/71.lean`.)
- [Ve05] Verstraëte, J., _Unavoidable cycle lengths in graphs_. J. Graph
  Theory (2005), 151-167. (Title/journal/year/pages from the `/latex/72`
  capture; volume DEFERRED. Note: the archived styled copy
  `deepmind/deepmind/72.lean` expands [Ve05] as a *different* 2005 Verstraëte
  paper — "A note on vertex-disjoint cycles", Combin. Probab. Comput. 14 —
  contradicting the site's own bibliography; that expansion is rejected here.)
- [LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd
  cycle problem_. arXiv:2010.15802 (2020); published in J. Amer. Math. Soc. 36
  (2023), 1191-1234. (arXiv datum from the `/latex/72` capture; published
  journal/volume/year/pages from the archived styled copy and the prior
  review — corroborated but not authoritative, DEFERRED at volume level.)
-/

open SimpleGraph

/--
A set A ⊆ ℕ has natural density zero: for every ε > 0, for all sufficiently large n,
|A ∩ {0, ..., n}| ≤ ε · n.

(This ε-N formulation is equivalent to the standard `|A ∩ [1, n]|/n → 0`: the two
counts differ by at most 1, which is absorbed since ε is arbitrary and N may be
taken ≥ 2/ε.)
-/
def HasDensityZero (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (Set.ncard (A ∩ Set.Iic n) : ℝ) ≤ ε * (n : ℝ)

/--
Erdős Problem #72 [Er94b, Er95, Er97b, Er97c] — PROVED (\$100 prize):
Is there a set A ⊂ ℕ of density 0 and a constant c > 0 such that every graph on
sufficiently many vertices with average degree ≥ c contains a cycle whose length is in A?

Solved affirmatively by Verstraëte [Ve05] (non-constructive proof).
Liu and Montgomery [LiMo20] proved this holds even when A is the set of powers of 2
(more generally, for any set of even numbers which doesn't grow too quickly) — contradicting
Erdős's own 'almost certain' belief that powers of 2 would *not* work. Bollobás [Bo77] had
earlier proved the analogue where A is an infinite arithmetic progression containing even
numbers (Problem #71).

Encoding notes: the problem is a yes/no question resolved affirmatively; following this
corpus's convention (no `answer()` macro with Mathlib-only imports), this theorem is the
direct assertion of the *true* direction, so the polarity matches the resolution.
"Average degree ≥ c" for a graph on n vertices is encoded multiplicatively as
2·|E(G)| ≥ c·n (avoiding division), and "sufficiently many vertices" by the ∃ N₀ threshold.
The constants are correctly ordered: A, c, N₀ are all chosen *before* the graph is
universally quantified. Mathlib's `Walk.IsCycle` forces cycle length ≥ 3, so degenerate
small elements of A (0, 1, 2) cannot be spuriously witnessed.
-/
theorem erdos_problem_72 :
    ∃ (A : Set ℕ), HasDensityZero A ∧
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), k ∈ A ∧ ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k :=
  sorry

/--
Liu–Montgomery variant [LiMo20], confirmed verbatim by the archived page ("Liu and
Montgomery proved that in fact this is true when A is the set of powers of 2"):
there is a constant c > 0 such that every graph on sufficiently many vertices with
average degree ≥ c contains a cycle whose length is a power of 2.

Since the powers of 2 form a density-zero set, this instantiates `erdos_problem_72`
with an explicit witness A = {2^m : m ∈ ℕ}, strengthening Verstraëte's
non-constructive solution — and contradicting Erdős's recorded belief that no such
c exists for powers of 2. (Fix not compile-verified; the review container cannot
run `lake build`.)
-/
theorem erdos_problem_72_powers_of_two :
    ∃ (c : ℝ), c > 0 ∧
    ∃ (N₀ : ℕ), ∀ (n : ℕ), n ≥ N₀ →
      ∀ (G : SimpleGraph (Fin n)) (hd : DecidableRel G.Adj),
        haveI := hd
        2 * (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) →
        ∃ (k : ℕ), (∃ m : ℕ, k = 2 ^ m) ∧
          ∃ (v : Fin n), ∃ (p : G.Walk v v), p.IsCycle ∧ p.length = k :=
  sorry
