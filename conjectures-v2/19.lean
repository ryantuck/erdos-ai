import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #19 (Erdős–Faber–Lovász Conjecture)

Verbatim source statement (erdosproblems.com/19):

> If $G$ is an edge-disjoint union of $n$ copies of $K_n$ then is $\chi(G)=n$?

The site phrases the problem as a yes/no question; this file asserts the
conjectured "yes" direction as a direct statement, the convention of this raw
corpus.

Status (page accessed 2026-02-24, page edition 23 January 2026; cross-checked
against the teorth/erdosproblems metadata mirror, `data/problems.yaml`, commit
a09c7a2 of 2026-08-14, which agrees): **DECIDABLE** — "Resolved up to a finite
check" — with a $500 prize.

Conjectured by Erdős, Faber, and Lovász (apparently "at a party in Boulder,
Colarado [sic] in September 1972" [Er81]). Kahn [Ka92] proved
χ(G) ≤ (1+o(1))·n (for which Erdős gave him a "consolation prize" of \$100).
Hindman [Hi81] proved the conjecture for n < 10. Various special cases have
been established by Romero and Sánchez-Arroyo [RoSa07], Araujo-Pardo and
Vázquez-Ávila [ArVa16], and Alesandroni [Al21]. Kang, Kelly, Kühn, Methuku,
and Osthus [KKKMO21] have proved the answer is yes for all sufficiently
large n.

In [Er97d] Erdős asks how large χ(G) can be if instead of asking for the
copies of K_n to be edge-disjoint we only ask for their intersections to be
triangle-free, or to contain at most one edge. (Open-ended "how large"
question; documented here, not formalized.)

In [Er93] Erdős and Füredi conjecture the generalisation that if G is the
union of n copies of K_n which pairwise intersect in at most k vertices, then
χ(G) ≤ kn. This has been proved for all sufficiently large n (not depending
on k) by Kang, Kelly, Kühn, Methuku, and Osthus [KKKMO24]. Furthermore, Horák
and Tuza [HoTu90] proved that χ(G) ≤ n^{3/2} if G is the union of n copies of
K_n, hence the conjecture also holds whenever k ≥ √n. The Erdős–Füredi
generalisation is formalized below (with a necessary k ≥ 1 hypothesis — see
the variant's docstring).

Problem sources cited on the page: [Er76b, p.171], [Er76c, p.9], [Er81],
[Er90], [Er92b], [Er93, p.341], [Er95], [Er97c], [Er97d], [Er97f],
[Va99, 3.57].

References (recovered offline from the archived page, the pipeline's
`erdosproblems.com/latex/19` fetch preserved in the session logs, and sibling
corpus files; honest stubs where noted — volumes/pages NOT guessed):

- [Er76b] Erdős, P. (1976). (Key-only stub: cited on the page at p.171; no
  bibliographic data recoverable offline.)
- [Er76c] Erdős, P. (1976). (Key-only stub: cited on the page at p.9; no
  bibliographic data recoverable offline.)
- [Er81] Erdős, P., _On the combinatorial problems which I would most like to
  see solved_. Combinatorica 1 (1981), 25-42. (Data from the /latex/19 fetch;
  volume from a sibling /latex recovery of the same key.)
- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to
  Paul Erdős (1990), 467-478. (Sibling-corpus consensus; not in the /latex/19
  extraction.)
- [Er92b] Erdős, P., _Some of my favourite problems in various branches of
  combinatorics_. Matematiche (Catania) 47 (1992), 231-240. (Sibling corpus.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in
  graph theory_. Quaestiones Mathematicae 16 (1993), 333-350. (Data from the
  /latex/19 fetch; volume from sibling corpus. This problem: p.341.)
- [Er95] Erdős, P. (1995). (Key-only stub: the corpus carries two conflicting
  expansions of this key; no page number is given for #19 to disambiguate.)
- [Er97c] Erdős, P., _Some of my favorite problems and results_. The
  mathematics of Paul Erdős, I (1997). (Sibling-majority reading; sibling
  files disagree on this key.)
- [Er97d] Erdős, P., _Some recent problems and results in graph theory_.
  Discrete Math. 164 (1997), no. 1-3, 81-85. (Data from the /latex/19 fetch;
  volume from sibling corpus.)
- [Er97f] Erdős, P. (1997). (Key-only stub; sibling files disagree on this
  key's expansion.)
- [Va99] Various, _Some of Paul's favorite problems_. Booklet produced for
  the conference "Paul Erdős and his mathematics", Budapest, July 1999
  (1999). This problem: §3.57. (Canonical entry from the sibling corpus.)
- [Hi81] Hindman, N., _On a conjecture of Erdős, Faber, and Lovász about
  n-colorings_. Canad. J. Math. (1981), 563-570. (/latex/19 fetch.)
- [Ka92] Kahn, J., _Coloring nearly-disjoint hypergraphs with n+o(n) colors_.
  J. Combin. Theory Ser. A (1992), 31-39. (/latex/19 fetch.)
- [HoTu90] Horák, P. and Tuza, Z., _A coloring problem related to the
  Erdős-Faber-Lovász conjecture_. J. Combin. Theory Ser. B (1990), 321-322.
  (/latex/19 fetch.)
- [RoSa07] Romero, D. and Sánchez-Arroyo, A., _Adding evidence to the
  Erdős-Faber-Lovász conjecture_. Ars Combin. (2007), 71-84. (/latex/19
  fetch.)
- [ArVa16] Araujo-Pardo, G. and Vázquez-Ávila, A., _A note on
  Erdős-Faber-Lovász conjecture and edge coloring of complete graphs_.
  Ars Combin. (2016), 287-298. (/latex/19 fetch.)
- [Al21] Alesandroni, G., _The Erdős-Faber-Lovász conjecture for weakly dense
  hypergraphs_. Discrete Math. (2021), Paper No. 112401, 7 pp. (/latex/19
  fetch. The page spells the name "Alesandroi" [sic].)
- [KKKMO21] Kang, D.Y., Kelly, T., Kühn, D., Methuku, A. and Osthus, D.,
  _A proof of the Erdős–Faber–Lovász conjecture_. Annals of Mathematics 198
  (2023), 537-618; arXiv:2101.04698. (Journal data from the styled sibling
  file; arXiv identifier from the /latex/19 fetch.)
- [KKKMO24] Kang, D.Y., Kelly, T., Kühn, D., Methuku, A. and Osthus, D.,
  _Solution to a problem of Erdős on the chromatic index of hypergraphs with
  bounded codegree_. Proc. London Math. Soc. (3) (2024), Paper No. e70011,
  32 pp. (/latex/19 fetch.)

No OEIS reference. Additional thanks (page): Sarosh Adenwalla, Alfaiz, and
dykang.

Tags: graph theory, chromatic number
https://www.erdosproblems.com/19
-/

/--
**Erdős–Faber–Lovász Conjecture (Erdős Problem #19)**:

If G is an edge-disjoint union of n copies of K_n, then χ(G) = n.

We formalize "G is an edge-disjoint union of n copies of K_n" as: there
exist n cliques (vertex sets), each of size n, such that
- each clique is a complete subgraph of G (an n-clique),
- any two distinct cliques share at most one vertex (equivalently, they are
  edge-disjoint, since two shared vertices would force a shared edge), and
- every edge of G lies in some clique.

Formalization notes:
- The source phrases the problem as a yes/no question ("… then is
  χ(G) = n?"); this theorem asserts the conjectured "yes" direction, which is
  the direction proved for all sufficiently large n by [KKKMO21] and for
  n < 10 by [Hi81] (status: DECIDABLE, resolved up to a finite check).
- The hypothesis `hn : 2 ≤ n` is load-bearing, not cosmetic: at n = 0 the
  clique family is empty, `hcover` forces G to be edgeless, and the
  conclusion χ(G) = 0 is false whenever V is nonempty (χ = 1). `1 ≤ n` would
  suffice (n = 1 holds trivially); `2 ≤ n` additionally drops only that
  trivial case.
- V is not required to be covered by the cliques, so G may contain isolated
  vertices outside the union. This is a harmless, truth-preserving
  generalization: clique 0 gives χ(G) ≥ n, and isolated vertices never raise
  the chromatic number of a graph that already needs n ≥ 2 colors.
- Distinctness of the n copies is implied: two equal cliques would share
  n ≥ 2 vertices, contradicting `hpairwise`.
-/
theorem erdos_problem_19 (n : ℕ) (hn : 2 ≤ n)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cliques : Fin n → Finset V)
    -- Each clique is a copy of K_n in G
    (hclique : ∀ i : Fin n, G.IsNClique n (cliques i))
    -- Any two distinct cliques share at most one vertex (edge-disjointness)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ((cliques i) ∩ (cliques j)).card ≤ 1)
    -- Every edge of G lies in some clique
    (hcover : ∀ u v : V, G.Adj u v → ∃ i : Fin n, u ∈ cliques i ∧ v ∈ cliques i) :
    G.chromaticNumber = n :=
  sorry

/--
**Erdős–Füredi Conjecture** (variant of Erdős Problem #19) [Er93]:

If G is the union of n copies of K_n which pairwise intersect in at most k
vertices, then χ(G) ≤ kn.

The page states the conjecture with no explicit lower bound on k, but at
k = 0 the statement is literally false: n pairwise-disjoint copies of K_n
(n ≥ 2) give χ(G) = n > 0 = k·n. We therefore formalize the corrected
version with the hypothesis `hk : 1 ≤ k`, following the pipeline precedent
for page-stated bounds that fail at degenerate parameters. Taking k = 1
recovers the upper-bound half of the Erdős–Faber–Lovász conjecture above.
The hypothesis `hn : 2 ≤ n` is needed for the same reason as in the main
theorem (at n = 0 the conclusion χ(G) ≤ 0 fails for nonempty edgeless V).

Proved for all sufficiently large n (not depending on k) by Kang, Kelly,
Kühn, Methuku, and Osthus [KKKMO24]. Horák and Tuza [HoTu90] proved
χ(G) ≤ n^{3/2} for any union of n copies of K_n, hence the conjecture holds
whenever k ≥ √n. (Their unconditional n^{3/2} bound needs a real-valued
exponent and is not formalized here.)

Statement added by the review pipeline from the recovered page content; NOT
compile-verified.
-/
theorem erdos_problem_19.variants.erdos_furedi (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cliques : Fin n → Finset V)
    -- Each clique is a copy of K_n in G
    (hclique : ∀ i : Fin n, G.IsNClique n (cliques i))
    -- Any two distinct cliques share at most k vertices
    (hpairwise : ∀ i j : Fin n, i ≠ j → ((cliques i) ∩ (cliques j)).card ≤ k)
    -- Every edge of G lies in some clique
    (hcover : ∀ u v : V, G.Adj u v → ∃ i : Fin n, u ∈ cliques i ∧ v ∈ cliques i) :
    G.chromaticNumber ≤ k * n :=
  sorry

end
