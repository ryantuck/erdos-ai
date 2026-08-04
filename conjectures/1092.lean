import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #1092

Source: https://www.erdosproblems.com/1092 [Er76c,p.4]
(page edition: 06 December 2025; accessed 2026-03-09; recovered from archived
pipeline session logs — the site is unreachable from this container).

Verbatim statement: "Let $f_r(n)$ be maximal such that, if a graph $G$ has the
property that every subgraph $H$ on $m$ vertices is the union of a graph with
chromatic number $r$ and a graph with $\leq f_r(m)$ edges, then $G$ has
chromatic number $\leq r+1$. Is it true that $f_2(n) \gg n$? More generally,
is $f_r(n) \gg_r n$?"

A conjecture of Erdős, Hajnal, and Szemerédi. The site's status banner is OPEN.
Remarks on the page: the problem is closely related to, but distinct from,
Erdős Problem #744; and Quanyu Tang notes in the comments that a construction
of Rödl [Ro82] disproves the first question, so that $f_2(n) \not\gg n$.
The general question (which, after Rödl, is open for $r \geq 3$) remains open.
Tags: graph theory, chromatic number. Additional thanks (per the page):
Quanyu Tang.

Reading of the statement: the defining property quantifies over subgraphs of
*every* size $m$ simultaneously, against a *function* bound $f_r(m)$ — note the
source's own mixing of $n$ and $m$ ("every subgraph $H$ on $m$ vertices …
$\leq f_r(m)$ edges"). "$f_r$ maximal" refers to the maximal growth rate of a
valid such function, and "$f_r(n) \gg n$" asks whether some *linear* function
is valid. A fixed-single-size reading is mathematically vacuous (see
`ForcesChromaticBound` below), and the function reading matches the closely
related problems #74 and #744 and Rödl's construction.

References (honest stubs; full bibliographic data not recoverable offline):

[Er76c] Erdős, P., _Problems in combinatorics and graph theory_ (1976), p. 4.
(Author/title/year from sibling files `deepmind/720.lean`, `deepmind/1091.lean`
in this repository, which carry the same key.)

[Ro82] Rödl, V. (1982). (Details not recoverable offline. Cited on
erdosproblems.com — also on problem #74, where the site states that Rödl proved
the hypergraph analogue and constructed a graph of chromatic number $\aleph_0$
all of whose $n$-vertex subgraphs can be made bipartite by deleting at most
$\epsilon n$ edges, for any fixed $\epsilon > 0$.)
-/

noncomputable section
open SimpleGraph Classical Finset

namespace Erdos1092

/--
The number of monochromatic edges of G within vertex set S under coloring c:
the number of edges {u,v} ⊆ S of G where c(u) = c(v).
-/
def monochromaticEdges {n r : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (c : Fin n → Fin r) : ℕ :=
  ((S ×ˢ S).filter (fun p : Fin n × Fin n =>
    p.1.val < p.2.val ∧ G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card

/--
`ForcesChromaticBound r f` says: every finite graph G, all of whose induced
subgraphs decompose as the union of a graph with chromatic number ≤ r and a
graph with at most f(m) edges (where m is the number of vertices of the
subgraph), has chromatic number ≤ r+1.

The decomposition is encoded via colorings: an m-vertex graph H is the union of
a graph with chromatic number ≤ r and a graph with ≤ k edges **iff** H admits
an r-coloring with at most k monochromatic edges (given the decomposition,
properly r-color the first part — the monochromatic edges all lie in the second
part; conversely, the monochromatic edges of a coloring form the second part).
Quantifying over induced subgraphs (i.e. vertex subsets S) suffices: a
non-induced subgraph on the same vertices decomposes whenever the induced one
does, by intersecting both parts with its edge set. Restricting to finite
graphs is equivalent to the general statement by De Bruijn–Erdős compactness.

Note: the hypothesis must range over subsets of **every** size against the
function bound `f`. A fixed-single-size version ("the maximum k such that
[every subgraph on exactly m vertices decomposes with ≤ k edges] implies
χ(G) ≤ r+1") is vacuous: for m ≥ r+3 the complete graph on m−1 vertices
satisfies the size-m hypothesis vacuously while having chromatic number
m−1 > r+1, so no k works; and for r = 2 any fixed size is also defeated by
high-girth graphs of large chromatic number, whose small subgraphs are forests.
-/
def ForcesChromaticBound (r : ℕ) (f : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    (∀ S : Finset (Fin n), ∃ c : Fin n → Fin r,
      (monochromaticEdges G S c : ℝ) ≤ f S.card) →
    G.chromaticNumber ≤ ((r + 1 : ℕ) : ℕ∞)

/--
Erdős Problem #1092, first question (DISPROVED) [Er76c,p.4]:

"Is it true that $f_2(n) \gg n$?" — that is, is there a constant $c > 0$ such
that every graph, all of whose $m$-vertex subgraphs are the union of a
bipartite graph and at most $c \cdot m$ edges, has chromatic number at most 3?

Quanyu Tang notes (on the problem page) that a construction of Rödl [Ro82]
disproves this: $f_2(n) \not\gg n$. We state the disproof: for every $c > 0$
the linear bound $m \mapsto c \cdot m$ fails to force chromatic number ≤ 3,
i.e. some graph is everywhere locally (bipartite + $\leq c m$ edges) yet has
chromatic number > 3. (Rödl's construction gives a graph of chromatic number
$\aleph_0$ with this local property; a finite counterexample follows by
De Bruijn–Erdős.)

Note the eventual-linear and everywhere-linear readings of "$\gg$" agree here:
if a valid (ℕ-valued) $f$ satisfies $f(m) \geq c m$ only for $m \geq N$, pick
any $c' \leq c$ with $c' < 1/N$; the everywhere-$c'm$ hypothesis forces 0
monochromatic edges on subsets of size $< N$ (there $c'm < 1$ and the count is
an integer) and is at most $cm \leq f(m)$ beyond, hence implies the
$f$-hypothesis, so validity transfers to the everywhere-linear bound $c'm$.
-/
theorem erdos_problem_1092_r2_disproof :
    ∀ c : ℝ, 0 < c → ¬ ForcesChromaticBound 2 (fun m => c * (m : ℝ)) :=
  sorry

/--
Erdős Problem #1092, general question (OPEN) [Er76c,p.4]:

"More generally, is $f_r(n) \gg_r n$?" — that is, for each $r$, is there a
constant $c_r > 0$ such that every graph, all of whose $m$-vertex subgraphs are
the union of a graph with chromatic number ≤ r and at most $c_r \cdot m$
edges, has chromatic number at most $r+1$?

As literally posed the general question includes $r = 2$, which Rödl's
construction [Ro82] answers negatively (see
`erdos_problem_1092_r2_disproof`); the surviving open content is $r \geq 3$,
which is what is stated here, in the conjectured ("yes") direction.
-/
theorem erdos_problem_1092_general (r : ℕ) (hr : 3 ≤ r) :
    ∃ c : ℝ, 0 < c ∧ ForcesChromaticBound r (fun m => c * (m : ℝ)) :=
  sorry

end Erdos1092
