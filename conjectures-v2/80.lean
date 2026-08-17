import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #80

Let $c > 0$ and let $f_c(n)$ be the maximal $m$ such that every graph $G$ with
$n$ vertices and at least $cn^2$ edges, where each edge is contained in at least
one triangle, must contain a book of size $m$, that is, an edge shared by at least
$m$ different triangles.

Estimate $f_c(n)$. In particular, is it true that $f_c(n) > n^{\epsilon}$ for some
$\epsilon > 0$? Or $f_c(n) \gg \log n$?

**Status: OPEN** (erdosproblems.com/80, accessed 2026-02-22; the teorth/erdosproblems
metadata mirror at 2026-08-14 agrees). Tags: graph theory, ramsey theory.

A problem of Erdős and Rothschild [Er87]. Alon and Trotter showed that, provided
$c < 1/4$, $f_c(n) \ll_c n^{1/2}$. Szemerédi observed that his regularity lemma
implies $f_c(n) \to \infty$. Edwards (unpublished) and Khadziivanov and Nikiforov
[KhNi79] proved independently that $f_c(n) \geq n/6$ when $c > 1/4$ (see Problem
#905). Fox and Loh [FoLo12] proved that $f_c(n) \le n^{O(1/\log\log n)}$ for all
$c < 1/4$, disproving the first conjecture of Erdős ($f_c(n) > n^\epsilon$).

The weaker conjecture $f_c(n) \gg \log n$ remains open. The best known lower bounds
for $f_c(n)$ are those from Szemerédi's regularity lemma, and as such remain very
poor.

See also Problem #600 (the inverse question: the minimal edge count $e(n,r)$ forcing
some edge into $r$ triangles) and the entry "CoveredInTriangles" in the graphs
problem collection at mathweb.ucsd.edu.

[Er87] Erdős, P. (1987). Problem source per erdosproblems.com/80; the site's
/bibs/Er87 entry was not captured in the session logs, so full bibliographic data
is DEFERRED. (Graph-theory sibling files in this corpus give "Some problems on
finite and infinite graphs", Logic and combinatorics, Contemp. Math. **65** (1987),
223–228, but the corpus is not internally consistent about this key.)

[FoLo12] Fox, J. and Loh, P.-S., _On a problem of Erdős and Rothschild on edges in
triangles_. Combinatorica (2012), 619–628. (Volume number absent from the recovered
source; DEFERRED.)

[KhNi79] Hadžiivanov, N. G. and Nikiforov, S. V., _Solution of a problem of P. Erdős
about the maximum number of triangles with a common edge in a graph_. C. R. Acad.
Bulgare Sci. (1979), 1315–1318. (Volume number absent from the recovered source;
DEFERRED.)
-/

/-- The number of common neighbors of `u` and `v` in `G`. When `{u, v}` is an edge
    of `G`, this equals the number of triangles containing that edge (i.e., the book
    size at that edge). -/
def bookSize {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) : ℕ :=
  ((G.neighborFinset u) ∩ (G.neighborFinset v)).card

/-- Every edge of `G` is contained in at least one triangle. -/
def EveryEdgeInTriangle {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ u v : V, G.Adj u v → 0 < bookSize G u v

/-- **Erdős Problem #80** (the conjecture $f_c(n) \gg \log n$, open): For every
    $c > 0$, there exist $C > 0$ and $N_0$ such that for all $n \geq N_0$, every
    graph on $n$ vertices with at least $cn^2$ edges, where every edge lies in a
    triangle, contains an edge that is in at least $C \log n$ triangles. -/
theorem erdos_problem_80 :
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 →
      EveryEdgeInTriangle G →
      ∃ u v : Fin n, G.Adj u v ∧
        (bookSize G u v : ℝ) ≥ C * Real.log (n : ℝ) := by
  sorry

/-- **Variant (solved; Szemerédi)**: the regularity lemma implies $f_c(n) \to \infty$
    for every fixed $c > 0$: for every book size $m$, all sufficiently large graphs
    meeting the hypotheses contain an edge in at least $m$ triangles. (Vacuously true
    for $c \geq 1/2$, where no graph has $cn^2$ edges once $n \geq 1$.) -/
theorem erdos_problem_80.variants.szemeredi :
    ∀ c : ℝ, c > 0 → ∀ m : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 →
      EveryEdgeInTriangle G →
      ∃ u v : Fin n, G.Adj u v ∧ m ≤ bookSize G u v := by
  sorry

/-- **Variant (solved; Edwards (unpublished), Khadziivanov–Nikiforov [KhNi79])**:
    for $c > 1/4$ one has $f_c(n) \geq n/6$ — every graph meeting the hypotheses
    contains an edge in at least $n/6$ triangles, for all sufficiently large $n$.
    See also Problem #905. -/
theorem erdos_problem_80.variants.edwards_khadziivanov_nikiforov :
    ∀ c : ℝ, c > 1 / 4 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 →
      EveryEdgeInTriangle G →
      ∃ u v : Fin n, G.Adj u v ∧ (bookSize G u v : ℝ) ≥ (n : ℝ) / 6 := by
  sorry

/-- **Variant (solved; Fox–Loh [FoLo12])**: for every $0 < c < 1/4$ there is $K > 0$
    such that for all sufficiently large $n$ there is a graph on $n$ vertices with at
    least $cn^2$ edges, every edge in a triangle, whose every edge lies in at most
    $n^{K/\log\log n}$ triangles — i.e. $f_c(n) \leq n^{O(1/\log\log n)}$. This
    disproves the first question of the problem ($f_c(n) > n^{\epsilon}$ for some
    $\epsilon > 0$) in the range $c < 1/4$. (For $c > 1/4$ that question has a
    positive answer via the $n/6$ bound above.) -/
theorem erdos_problem_80.variants.fox_loh :
    ∀ c : ℝ, 0 < c → c < 1 / 4 →
    ∃ K : ℝ, K > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      (G.edgeFinset.card : ℝ) ≥ c * (n : ℝ) ^ 2 ∧
      EveryEdgeInTriangle G ∧
      ∀ u v : Fin n, G.Adj u v →
        (bookSize G u v : ℝ) ≤ (n : ℝ) ^ (K / Real.log (Real.log (n : ℝ))) := by
  sorry

end
