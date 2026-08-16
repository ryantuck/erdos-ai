import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Basic

open SimpleGraph Finset

/-!
# Erdős Problem #23

Can every triangle-free graph on $5n$ vertices be made bipartite by deleting
at most $n^2$ edges?

**Status: OPEN (FALSIFIABLE)** — banner tooltip: "Open, but could be
disproved with a finite counterexample." (erdosproblems.com/23, page last
edited 18 January 2026, accessed 2026-03-05; the teorth/erdosproblems
metadata mirror agrees: state "falsifiable", last update 2025-08-31.)

The blow-up of $C_5$ shows that this would be the best possible. The best
known bound is due to Balogh, Clemen, and Lidický [BCL21], who proved that
deleting at most $1.064n^2$ edges suffices.

In [Er92b] Erdős asks, more generally, if a graph on $(2k+1)n$ vertices in
which every odd cycle has size $\geq 2k+1$ can be made bipartite by deleting
at most $n^2$ edges. (Taken literally for every $k$ this is false at $k = 1$
— see the variant below — so the formalized variant restricts to $k \geq 2$;
$k = 2$ is exactly this problem.)

This problem is #58 in Extremal Graph Theory in the graphs problem
collection.

## References

Problem sources: [Er71], [EFPS88], [Er90], [Er93, p.343], [Er97b], [Er97f].

- [Er71] Erdős, P., *Some unsolved problems in graph theory and
  combinatorial analysis*. Combinatorial Mathematics and its Applications
  (Proceedings of Conference, Oxford, 1969) (1971), 97-109.
- [EFPS88] Erdős, P., Faudree, R. J., Pach, J., and Spencer, J. H., *How to
  make a graph bipartite*. J. Combin. Theory Ser. B 45 (1988), 86-98.
- [Er90] Erdős, P., *Some of my favourite unsolved problems*. A tribute to
  Paul Erdős (1990), 467-478.
- [Er92b] Erdős, P., *Some of my favourite problems in various branches of
  combinatorics*. Matematiche (Catania) 47 (1992), 231-240.
- [Er93] Erdős, P., *Some of my favorite solved and unsolved problems in
  graph theory*. Quaestiones Mathematicae 16 (1993), 333-350.
- [Er97b] Erdős, P., *Some of my favourite problems which recently have been
  solved*, Proceedings of the International Conference on Discrete
  Mathematics (ICDM) (1997).
- [Er97f] Erdős, P., *Some unsolved problems*. Combinatorics, geometry and
  probability (Cambridge, 1993) (1997), 1-10.
- [BCL21] Balogh, J., Clemen, F. C., and Lidický, B., *Max Cuts in
  Triangle-free Graphs*. arXiv:2103.14179 (2021).

Provenance of bibliographic data: the erdosproblems.com/23 page capture in
the session logs lists the citation keys only (the site loads reference data
via separate `/bibs/` requests, not captured; no `/latex/23` fetch is in the
logs). The entries for [Er71], [Er90], [Er92b], [Er93], [Er97b], [Er97f] are
taken from sibling files of this corpus that share the same site-global keys
(`deepmind/deepmind/24.lean` — the neighbouring problem, also a
triangle-free-graphs-on-$5n$-vertices problem — and
`deepmind/deepmind/1008.lean`). The [BCL21] title/arXiv id is taken from the
upstream google-deepmind/formal-conjectures file for this problem (HEAD of
2026-08-16). The [EFPS88] entry is from reviewer knowledge only — no session
artifact carries it — and, like all of the above, is NOT verified against
`erdosproblems.com/latex/23`.

Related OEIS sequences: A389646.
Additional thanks (per the page): Casey Tompkins.
Formalised statement? Yes (upstream:
google-deepmind/formal-conjectures `FormalConjectures/ErdosProblems/23.lean`;
mirror records formalized "yes", 2026-02-17).

Tags: graph theory
https://www.erdosproblems.com/23
-/

/--
Erdős Problem #23 [Er71, EFPS88, Er90, Er93, Er97b, Er97f]:

Can every triangle-free graph on 5n vertices be made bipartite by deleting
at most n² edges?

The blow-up of C₅ shows this would be best possible. The best known bound
is due to Balogh, Clemen, and Lidický [BCL21], who proved that deleting at
most 1.064n² edges suffices.

We formalise "made bipartite by deleting at most n² edges" as: there exists
a 2-colouring f such that the number of monochromatic edges is at most n².
This is equivalent to the deletion formulation: deleting the monochromatic
edges of any 2-colouring leaves a bipartite graph, and conversely if
deleting some set E' of edges leaves a bipartite graph then the bipartition
2-colouring makes every monochromatic edge of G lie in E'. The filter
counts each unordered monochromatic edge exactly once via `p.1 < p.2`.

The source poses this as a yes/no question, status OPEN (falsifiable). The
raw pipeline has no `answer()` elaborator; per this corpus's convention the
conjectured ("yes") direction is asserted directly.
-/
theorem erdos_problem_23 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    ∃ (f : Fin (5 * n) → Fin 2),
      ((univ ×ˢ univ).filter (fun p : Fin (5 * n) × Fin (5 * n) =>
        p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ f p.1 = f p.2)).card ≤ n ^ 2 :=
  sorry

/--
**Variant (Balogh–Clemen–Lidický bound [BCL21], page-confirmed):** the best
known partial result — every triangle-free graph on 5n vertices can be made
bipartite by deleting at most 1.064n² edges.

The page states the bound as $1.064n^2$; since $1.064 = 133/125$, the
inequality `card ≤ 1.064 * n²` is encoded in ℕ as
`125 * card ≤ 133 * n²`, avoiding real-number casts. (At n = 1 this allows
at most one deletion, which is correct: the only non-bipartite triangle-free
graph on 5 vertices is C₅ itself, and one deletion suffices.)
-/
theorem erdos_problem_23.variants.balogh_clemen_lidicky :
    ∀ (n : ℕ) (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
    haveI := h
    G.CliqueFree 3 →
    ∃ (f : Fin (5 * n) → Fin 2),
      125 * ((univ ×ˢ univ).filter (fun p : Fin (5 * n) × Fin (5 * n) =>
        p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ f p.1 = f p.2)).card ≤ 133 * n ^ 2 :=
  sorry

/--
**Variant (tightness via the blow-up of C₅, page-confirmed):** "The blow-up
of $C_5$ shows that this would be the best possible." For every n there is a
triangle-free graph on 5n vertices — the balanced blow-up of the 5-cycle,
each vertex replaced by an independent set of size n — for which every
2-colouring leaves at least n² monochromatic edges, i.e. which cannot be
made bipartite by deleting fewer than n² edges.

The witness graph is existentially quantified (the blow-up construction
lives in the omitted proof), so no new graph-construction machinery is
needed at statement level. The decidability instance is also existentially
quantified, mirroring the main theorem's explicit-instance device; this is
harmless since `DecidableRel G.Adj` is a subsingleton and always classically
inhabited.
-/
theorem erdos_problem_23.variants.blow_up_tight :
    ∀ n : ℕ, ∃ (G : SimpleGraph (Fin (5 * n))) (h : DecidableRel G.Adj),
      haveI := h
      G.CliqueFree 3 ∧
      ∀ f : Fin (5 * n) → Fin 2,
        n ^ 2 ≤ ((univ ×ˢ univ).filter (fun p : Fin (5 * n) × Fin (5 * n) =>
          p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ f p.1 = f p.2)).card :=
  sorry

/--
**Variant (odd-girth generalization [Er92b], page-confirmed, corrected):**
"In [Er92b] Erdős asks, more generally, if a graph on $(2k+1)n$ vertices in
which every odd cycle has size $\geq 2k+1$ can be made bipartite by deleting
at most $n^2$ edges."

The page states no restriction on k, but the literal all-k statement is
false at k = 1: there the hypothesis "every odd cycle has length ≥ 3" is
vacuous, yet K₆ (k = 1, n = 2) has 15 edges and maximum cut 9, so it needs
6 > n² = 4 deletions. (At k = 0 the statement is vacuously true: any graph
on n vertices has at most n(n-1)/2 < n² edges.) Following the corrected-
formalization precedent for literally-false page bounds, the variant is
stated for k ≥ 2; the case k = 2 is exactly the main problem, since "every
odd cycle has length ≥ 5" is equivalent to triangle-freeness.

"Every odd cycle has size ≥ 2k+1" is encoded via closed walks: every closed
walk that is a cycle and has odd length has length ≥ 2k+1. This requires
`Mathlib.Combinatorics.SimpleGraph.Paths` (added import, following the
added-import precedent of `conjectures-v2/20.lean`/`22.lean`; compile risk
flagged).
-/
theorem erdos_problem_23.variants.odd_girth_generalization :
    ∀ (k n : ℕ), 2 ≤ k →
    ∀ (G : SimpleGraph (Fin ((2 * k + 1) * n))) (h : DecidableRel G.Adj),
    haveI := h
    (∀ (v : Fin ((2 * k + 1) * n)) (w : G.Walk v v),
      w.IsCycle → Odd w.length → 2 * k + 1 ≤ w.length) →
    ∃ (f : Fin ((2 * k + 1) * n) → Fin 2),
      ((univ ×ˢ univ).filter
        (fun p : Fin ((2 * k + 1) * n) × Fin ((2 * k + 1) * n) =>
          p.1 < p.2 ∧ G.Adj p.1 p.2 ∧ f p.1 = f p.2)).card ≤ n ^ 2 :=
  sorry
