import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths

open SimpleGraph

/--
Erdős Problem #64 ($1000 prize) (Conjectured by Erdős and Gyárfás
[Er93 p.343, Er94b, Er95 p.174, Er96, Er97b, Er97c]):

"Does every finite graph with minimum degree at least 3 contain a cycle of length
$2^k$ for some $k\geq 2$?" (Verbatim from the archived problem page, last edited
18 January 2026, accessed 2026-03-05. Status banner: **FALSIFIABLE** — "Open, but
could be disproved with a finite counterexample." Status cross-checked against the
teorth/erdosproblems metadata mirror, `data/problems.yaml` entry 64: falsifiable,
last update 2025-08-31, prize $1000. The upstream google-deepmind/formal-conjectures
repository (HEAD dd1c2be, checked 2026-08-16) carries `ErdosProblems/64.lean` with
this same proposition as the RHS of `answer(sorry) ↔ …` under
`@[category research open]`.)

**Polarity note.** The problem is an *open yes/no question*; this raw pipeline has no
`answer()` elaborator (plain Mathlib imports), so per the corpus convention the
theorem is a direct assertion of one direction with the choice documented. The
direction asserted here is the **affirmative** — the statement known in the
literature as the *Erdős–Gyárfás conjecture*, and exactly the upstream
formal-conjectures RHS. This choice is deliberate, even though the page records that
Erdős and Gyárfás themselves "believed the answer must be negative, and in fact for
every $r$ there must be a graph of minimum degree at least $r$ without a cycle of
length $2^k$ for any $k\geq 2$": that strengthened negative belief was **disproved**
by Liu and Montgomery [LiMo20], who solved the question in the affirmative whenever
the minimum degree exceeds some absolute constant (see
`erdos_problem_64.variants.liu_montgomery`). The minimum-degree-3 case asserted here
remains open in both directions; a finite counterexample would refute this theorem.

Further remarks from the page: Liu and Montgomery prove a much stronger result — if
the average degree of $G$ is sufficiently large then there is some large integer
$\ell$ such that $G$ contains a cycle of every even length
$m \in [(\log \ell)^8, \ell]$ (recorded here in prose only: formalizing it needs
`Real.log` and an average-degree definition, neither present in this file). An
infinite tree with minimum degree $3$ shows the answer is trivially false for
infinite graphs — hence `[Fintype V]` below is essential (an infinite-graph variant
is not formalized here: Mathlib's `minDegree` is finite-only). This problem is #69
in the Extremal Graph Theory section of the graphs problem collection. Tags: graph
theory, cycles. No OEIS references. 1 comment on the page (content not recoverable
offline).

Encoding notes: `G.minDegree` is Mathlib's minimum vertex degree, whose junk value
on an empty vertex type is `0`, so `3 ≤ G.minDegree` in particular forces `V`
nonempty — the empty graph (informal min degree $= \inf \emptyset = +\infty$) is
excluded, matching the problem's intent. A cycle of length $m$ is encoded as a
closed walk `p : G.Walk v v` with `p.IsCycle` (nonempty, no repeated edges, no
repeated interior vertices) and `p.length = m`; this is the standard Mathlib
encoding of a subgraph cycle, and in a simple graph any cycle has length ≥ 3, so
`p.length = 2 ^ k` with `2 ≤ k` captures exactly the source's "$2^k$ for some
$k \geq 2$" (lengths $1 = 2^0$ and $2 = 2^1$ are impossible in a simple graph
anyway).

References (the page's `/latex/64` payload was NOT captured in the session logs;
entries below are honest stubs from sibling corpus files, all DEFERRED against the
live source — nothing is fabricated):

- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae (1993), 333–350. (Corpus-consensus entry; the
  page's pointer [Er93, p.343] falls inside this page range, corroborating the
  entry.)
- [Er94b] Erdős, P. (1994). (Key from the page; sibling corpus files expand this
  key inconsistently — key-only stub.)
- [Er95] Erdős, P. (1995). (Key from the page; sibling corpus files carry
  conflicting expansions of this key. The page's pointer [Er95, p.174] falls inside
  the page range of the corpus-majority candidate _Some of my favourite problems in
  number theory, combinatorics, and geometry_, Resenhas (1995), 165–186, but the
  conflict is unresolved offline — key-only stub.)
- [Er96] Erdős, P., _Some of my favourite problems on cycles and colourings_.
  Tatra Mt. Math. Publ. (1996), 7–9. (From the log-recovered `/latex/57`
  extraction of the same key; DEFERRED for this page.)
- [Er97b] Erdős, P. (1997). (Key from the page; sibling corpus files expand this
  key inconsistently — key-only stub.)
- [Er97c] Erdős, P. (1997). (Key from the page; sibling corpus files expand this
  key inconsistently — cf. `conjectures-v2/19.lean` vs `conjectures-v2/46.lean` —
  key-only stub.)
- [LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle
  problem_. J. Amer. Math. Soc. **36** (2023), 1191–1234; arXiv:2010.15802 (2020).
  (Corpus-consensus entry; DEFERRED against the live source.)

Source: https://www.erdosproblems.com/64
-/
theorem erdos_problem_64 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 3 ≤ G.minDegree) :
    ∃ k : ℕ, 2 ≤ k ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ k :=
  sorry

/--
Erdős Problem #64, Liu–Montgomery theorem (page-confirmed) [LiMo20]:

"This was solved in the affirmative if the minimum degree is larger than some
absolute constant by Liu and Montgomery (therefore disproving the above stronger
conjecture of Erdős and Gyárfás)."

There is an absolute constant $C$ such that every finite graph with minimum degree
at least $C$ contains a cycle of length $2^k$ for some $k \geq 2$. **SOLVED** —
proved by Liu and Montgomery [LiMo20]. Classically this statement is exactly the
negation of the Erdős–Gyárfás strengthened conjecture "for every $r$ there must be
a graph of minimum degree at least $r$ without a cycle of length $2^k$ for any
$k \geq 2$": $\neg(\forall r, \exists G,\ r \le \delta(G) \wedge$ no such cycle$)
\iff (\exists C, \forall G,\ C \le \delta(G) \to$ some such cycle$)$ — so no
separate "disproof" variant is needed. Quantifier-order note: `∃ C` sits *outside*
the `∀ V G`, making $C$ an absolute constant rather than graph-dependent, and the
statement is substantive for every value of $C$ (graphs of arbitrarily large
minimum degree exist), so the existential cannot be discharged degenerately.

NOTE: this variant was added by the Fable review (page-confirmed enrichment) and is
NOT compile-verified.
-/
theorem erdos_problem_64.variants.liu_montgomery :
    ∃ C : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
      C ≤ G.minDegree →
      ∃ k : ℕ, 2 ≤ k ∧
        ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ k :=
  sorry
