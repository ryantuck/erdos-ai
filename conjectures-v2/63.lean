import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Erdős Problem 63

*Reference:* [erdosproblems.com/63](https://www.erdosproblems.com/63)
(accessed 2026-02-22; page content recovered from two agreeing archived captures in the
original pipeline session's log — a raw `html/63.html` Read and a tidied problem-box
Read, both in `claude-session-logs/751b767c-…jsonl` — the live site is unreachable from
the review container).

Statement (verbatim from the site): "Does every graph with infinite chromatic number
contain a cycle of length $2^n$ for infinitely many $n$?" Cited on the page as
[Er93,p.342][Er94b][Er95][Er95d][Er96][Er97b]. Tags: graph theory | chromatic number |
cycles. No prize; no OEIS entry (mirror lists "N/A").

Status: **PROVED** (tooltip: "This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (`data/problems.yaml`, commit a09c7a2, 2026-08-14)
agrees: status "proved" (last update 2025-08-31); formalized: no. The upstream
google-deepmind/formal-conjectures repository (HEAD dd1c2be, checked 2026-08-16) has no
`ErdosProblems/63.lean`, matching the page's "Formalised statement? No".

Remarks from the page: "Conjectured by Mihók and Erdős. It is likely that $2^n$ can be
replaced by any sufficiently quickly growing sequence (e.g. the squares)." David Penman
has observed that the answer is certainly yes if the graph has *uncountable* chromatic
number, since by a result of Erdős and Hajnal [ErHa66] such a graph must contain
arbitrarily large finite complete bipartite graphs (see also Theorem 3.17 of Reiher
[Re24]). Zach Hunter has observed that the full conjecture follows from the work of Liu
and Montgomery [LiMo20]: if $G$ has infinite chromatic number then, for infinitely many
$r$, it contains a finite connected subgraph $G_r$ with chromatic number $r$ (via the
de Bruijn–Erdős theorem [dBEr51]); each $G_r$ contains a subgraph $H_r$ with minimum
degree at least $r-1$, and by Theorem 1.1 of [LiMo20] there is some
$\ell_r \geq r^{1-o(1)}$ such that $H_r$ contains a cycle of every even length in
$[(\log \ell_r)^8, \ell_r]$. See also Problem #64 (finite graphs of minimum degree at
least 3 and a cycle of length a power of two). Additional thanks (per the page): Zach
Hunter and David Penman. 1 comment on the problem.

References (per-entry provenance; the page's `/latex/63` and `/bibs/` payloads were NOT
captured in the logs, so journal/volume data below is corpus-consensus or reviewer
knowledge, marked DEFERRED — nothing is fabricated):

- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
  Quaestiones Mathematicae (1993), 333–350. The page cites [Er93, p.342], which falls
  inside this page range, corroborating the entry. (Corpus-consensus entry; DEFERRED.)
- [Er94b] [Er95] [Er95d] [Er96] [Er97b] Erdős, P. — further papers of Erdős where this
  problem appears (keys from the page; sibling corpus files expand these keys
  inconsistently, so they are left as key-only stubs — DEFERRED).
- [ErHa66] Erdős, P. and Hajnal, A., _On chromatic number of graphs and set-systems_.
  Acta Math. Acad. Sci. Hungar. **17** (1966), 61–99. (Corpus-consensus entry, e.g.
  `conjectures/1068.lean` and `deepmind/deepmind/63.lean`; DEFERRED against the live
  source.)
- [LiMo20] Liu, H. and Montgomery, R., _A solution to Erdős and Hajnal's odd cycle
  problem_. J. Amer. Math. Soc. **36** (2023), 1191–1234; arXiv:2010.15802 (2020).
  (Corpus-consensus entry plus reviewer knowledge; DEFERRED against the live source.)
- [Re24] Reiher, C., _Graphs of large chromatic number_ (Theorem 3.17 is cited by the
  page). (Key from the page; no expansion recoverable offline — key-only stub,
  DEFERRED.)
- [dBEr51] de Bruijn, N. G. and Erdős, P., _A colour problem for infinite graphs and a
  problem in the theory of relations_. Indag. Math. **13** (1951), 369–373.
  (Corpus-consensus entry, cf. `deepmind/deepmind/110.lean`; DEFERRED against the live
  source.)
-/

open SimpleGraph

/--
Erdős Problem #63 (Conjectured by Mihók and Erdős [Er93,p.342][Er94b][Er95][Er95d][Er96][Er97b]):
Does every graph with infinite chromatic number contain a cycle of length 2^n for
infinitely many n? (PROVED, via Liu-Montgomery [LiMo20].)

Formalized as: for every graph G with infinite chromatic number, for every bound N,
there exists n ≥ N such that G contains a cycle of length 2^n.

Status: PROVED — this direct assertion is the true direction, per the page banner
("This has been solved in the affirmative."), the metadata mirror (proved, 2025-08-31),
and Zach Hunter's derivation from [LiMo20]. `G.chromaticNumber = ⊤` (with
`chromaticNumber : ℕ∞` an infimum over the finitely-colorable cardinalities, so `⊤`
exactly when no finite coloring exists) encodes infinite chromatic number. Cycles in a
`SimpleGraph` have length ≥ 3, so the lengths $2^0 = 1$ and $2^1 = 2$ are unachievable;
this is harmless under the "infinitely many n" quantifier (the content lives at n ≥ 2).
-/
theorem erdos_problem_63 {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ n :=
  sorry

/--
Page-confirmed variant (stated on the page as known, before the full solution): "David
Penman has observed that this is certainly true if the graph has uncountable chromatic
number, since by a result of Erdős and Hajnal [ErHa66] such a graph must contain
arbitrarily large finite complete bipartite graphs."

"Uncountable chromatic number" is encoded as: no proper coloring by any countable color
type (i.e. χ(G) > ℵ₀), following the encoding used for problem #62 in this corpus. The
conclusion is the main statement's conclusion verbatim. (A fortiori this instance also
follows from `erdos_problem_63`; it is recorded because the page singles it out as the
independently-known case.)

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_63.variants.uncountable_chromatic {V : Type*} (G : SimpleGraph V)
    (hχ : ∀ (α : Type*) [Countable α], IsEmpty (G.Coloring α)) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = 2 ^ n :=
  sorry

/--
Page-confirmed variant (OPEN — this states the speculated direction of a remark, not a
known theorem): "It is likely that $2^n$ can be replaced by any sufficiently quickly
growing sequence (e.g. the squares)." This formalizes the squares instance: every graph
with infinite chromatic number contains a cycle of length $n^2$ for infinitely many $n$.
(The general "any sufficiently quickly growing sequence" form is left unformalized —
the page does not pin down "sufficiently quickly growing". Squares of $n \le 1$ give
unachievable cycle lengths $0, 1$; harmless under the "infinitely many n" quantifier.)

NOTE: this variant was added by the Fable review and is NOT compile-verified.
-/
theorem erdos_problem_63.variants.squares {V : Type*} (G : SimpleGraph V)
    (hχ : G.chromaticNumber = ⊤) :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n ^ 2 :=
  sorry
