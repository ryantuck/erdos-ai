import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic

/-!
# Erdős Problem 24

*Reference:* [erdosproblems.com/24](https://www.erdosproblems.com/24)
(archived capture accessed 2026-02-22)

**Problem (verbatim from the source page):** "Does every triangle-free graph on
$5n$ vertices contain at most $n^5$ copies of $C_5$?"

**Status:** PROVED ("This has been solved in the affirmative."). The
teorth/erdosproblems metadata mirror (clone of 2026-08-14) records the current
status as "proved (Lean)" (last update 2026-04-23): the statement has since been
formalized upstream (google-deepmind/formal-conjectures, `erdos_24`, with a
`formal_proof` link to plby/lean-proofs `Erdos24.lean`) and the proof verified
in Lean. The page capture's "Formalised statement? No" is stale relative to the
mirror (formalized: yes, 2026-08-03).

**Remarks (from the source page):** Győri proved this with $1.03n^5$, which has
been improved by Füredi. The answer is yes, as proved independently by Grzesik
[Gr12] and Hatami, Hladký, Král, Norine, and Razborov [HHKNR13]. In [Er92b] and
[Er97f] Erdős asks more generally: if $r \geq 5$ is odd and a graph has $rn$
vertices and the smallest odd cycle has size $r$, then is the number of cycles
of size $r$ at most $n^r$? (Formalized below as
`erdos_problem_24.variants.odd_cycles`.)

The bound $n^5$ is tight: the balanced blow-up of $C_5$ (five independent parts
of size $n$, complete bipartite graphs between cyclically consecutive parts) is
triangle-free and contains exactly $n^5$ copies of $C_5$. (Standard fact, not
stated on the page; cf. `blowupC5` in the upstream formalization of Problem 23.)

**Source citation keys** (from the page): [Er90], [Er92b], [Er97b], [Er97f]
(problem sources); [Gr12], [HHKNR13] (solutions, cited in the remarks).

## References

Provenance: the entries for [Er92b], [Er97f], [Gr12], [HHKNR13] were recovered
from the original pipeline's fetch of `erdosproblems.com/latex/24` (session
logs; no volume numbers appear in that extraction). [Er90] and [Er97b] are not
among the `/latex/24` bibitems; their entries below are corpus-sourced
(google-deepmind/formal-conjectures at HEAD 2026-08-16, corroborated across
several sibling files) and remain unverified against the site. The volume
number **47** for [Er92b] is likewise corpus-sourced (upstream `593.lean`, this
repo's `deepmind/deepmind/24.lean`), not from the `/latex/24` extraction.
Earlier corpus copies gave [Er97b] as "Some of my favourite problems which
recently have been solved, Proceedings ICDM (1997)"; the current upstream
corpus consistently uses the entry below. Site verification: DEFERRED.

- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to Paul
  Erdős (1990), 467-478.
- [Er92b] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Matematiche (Catania) 47 (1992), 231-240.
- [Er97b] Erdős, P., _Some old and new problems in various branches of
  combinatorics_. Discrete Math. (1997), 227-231.
- [Er97f] Erdős, P., _Some unsolved problems_. Combinatorics, geometry and
  probability (Cambridge, 1993) (1997), 1-10.
- [Gr12] Grzesik, A., _On the maximum number of five-cycles in a triangle-free
  graph_. J. Combin. Theory Ser. B (2012), 1061-1066.
- [HHKNR13] Hatami, H., Hladký, J., Král, D., Norine, S., and Razborov, A.,
  _On the number of pentagons in triangle-free graphs_. J. Combin. Theory
  Ser. A (2013), 722-732.

Tags: graph theory. Related OEIS sequences: "Possible" (none listed).
Additional thanks to: Casey Tompkins, Tuan Tran.
-/

open SimpleGraph Finset

/--
Erdős Problem #24 (Proved by Grzesik [Gr12] and Hatami-Hladký-Král-Norine-Razborov [HHKNR13]):
Every triangle-free graph on 5n vertices contains at most n^5 copies of C_5.

The source poses this as a yes/no question ("Does every triangle-free graph on
$5n$ vertices contain at most $n^5$ copies of $C_5$?"), answered affirmatively;
per this pipeline's convention for solved problems, the true direction is
asserted directly.

We count labeled 5-cycles: injective functions f : Fin 5 → Fin (5n) such that
f(i) is adjacent to f((i+1) mod 5) for all i. Each unordered C_5 yields exactly
10 labeled 5-cycles (5 rotations × 2 reflections), so the labeled count bound
is 10 · n^5. The bound is tight for the balanced blow-up of C_5.
-/
theorem erdos_problem_24 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    (Finset.univ.filter (fun (f : Fin 5 → Fin (5 * n)) =>
      Function.Injective f ∧
      ∀ i : Fin 5, G.Adj (f i) (f (i + 1)))).card
    ≤ 10 * n ^ 5 :=
  sorry

/--
The general odd-cycle question of Erdős ([Er92b], [Er97f], quoted on the page):
"if $r \geq 5$ is odd and a graph has $rn$ vertices and the smallest odd cycle
has size $r$ then is the number of cycles of size $r$ at most $n^r$?" No
resolution is recorded on the recovered page capture.

We write the odd number as r = 2m + 1 with m ≥ 2 (so that `Fin (2*m+1)` has the
`NeZero` instance needed for the cyclic successor `i + 1`), and we encode "the
smallest odd cycle has size r" as odd girth ≥ r: for every odd k with
3 ≤ k < r there is no k-cycle, a k-cycle being an injective map
g : Fin k → V with g(i) adjacent to g(i+1) for all i (indices mod k). This
allows graphs with no odd cycle at all, for which the conclusion holds
trivially (an r-cycle would itself be an odd cycle), so the reading is
faithful. As in the main statement we count labeled cycles: each unordered
C_r yields exactly 2r labeled copies (r rotations × 2 reflections), so the
bound n^r on unordered copies becomes 2·r·n^r = 2·(2m+1)·n^(2m+1).

For m = 2 (r = 5) the hypothesis is exactly triangle-freeness (the only
shorter odd cycle is C_3) and the statement reduces to `erdos_problem_24`.
-/
theorem erdos_problem_24.variants.odd_cycles :
    ∀ (m n : ℕ), 2 ≤ m →
    ∀ (G : SimpleGraph (Fin ((2 * m + 1) * n))) (h : DecidableRel G.Adj),
    haveI := h
    (∀ j : ℕ, 1 ≤ j → j < m →
      ¬ ∃ g : Fin (2 * j + 1) → Fin ((2 * m + 1) * n),
          Function.Injective g ∧
          ∀ i : Fin (2 * j + 1), G.Adj (g i) (g (i + 1))) →
    (Finset.univ.filter (fun (f : Fin (2 * m + 1) → Fin ((2 * m + 1) * n)) =>
      Function.Injective f ∧
      ∀ i : Fin (2 * m + 1), G.Adj (f i) (f (i + 1)))).card
    ≤ 2 * (2 * m + 1) * n ^ (2 * m + 1) :=
  sorry
