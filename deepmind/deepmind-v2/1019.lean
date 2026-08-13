/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 1019

A planar graph on $n$ vertices with $3n - 6$ edges (the maximum possible) is called
saturated. Does every graph on $n$ vertices with at least
$\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges contain a saturated (maximal)
planar subgraph on more than 3 vertices?

This was solved in the affirmative by Simonovits in his PhD thesis: every such graph must
contain either a $K_4$ or a $C_l + 2K_1$ (a cycle joined to two independent vertices) for
some $l \geq 3$, and both are saturated planar graphs. A proof is given by Cambie in the
comments on the problem page.

A saturated planar graph on $3$ vertices is a triangle, which by Turán's theorem is
contained in every graph on $n$ vertices with $\lfloor n^2/4 \rfloor + 1$ edges. Erdős
[Er71] writes it is "easy to construct" a graph on $n$ vertices with
$\lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ edges (one less than the threshold
above) which contains no saturated planar graph with more than $3$ vertices, so the
threshold is sharp. Erdős [Er69c] proved that every graph with $n$ vertices and
$\lfloor n^2/4 \rfloor + k$ edges contains a saturated planar graph on $\gg k/n$
vertices, answering a question of Dirac.

*Reference:* [erdosproblems.com/1019](https://www.erdosproblems.com/1019)
(problem cited there as [Er64f] [Er69c] [Er71, p.102]; page last edited 08 December
2025, archived copy accessed 2026-02-22)

[Er64f] Erdős, P., _On extremal problems of graphs and generalized graphs_. Israel J. Math. **2**
(1964), 183–190.

[Er69c] Erdős, P., _Über die in Graphen enthaltenen saturierten planaren Graphen_.
Mathematische Nachrichten (1969), 13–17.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proceedings of Conference, Oxford, 1969)
(1971), 97–109.
-/

open SimpleGraph Finset

namespace Erdos1019

/-- A graph is planar if it can be embedded in the plane without edge crossings.
Mathlib does not yet have a formalization of graph planarity; we axiomatize it
here as an opaque predicate. -/
opaque IsPlanar {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop

/--
Erdős Problem 1019 [Er64f, Er69c, Er71]:

Does every graph on $n$ vertices with at least
$\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges contain a saturated planar graph
with more than $3$ vertices — that is, a subgraph on some $k > 3$ vertices which is
planar with exactly $3k - 6$ edges (the maximum possible)?

Solved in the affirmative by Simonovits (PhD thesis), hence `answer(True)`.

The hypothesis $n \geq 4$ excludes degenerate small cases: for $n \in \{1, 2, 3\}$ the
edge threshold exceeds $\binom{n}{2}$ (so the statement is vacuous there), while for
$n = 0$ the empty graph meets the (zero) edge threshold yet has no subgraph on more than
$3$ vertices at all, which would falsify an unrestricted universal statement.
-/
@[category research solved, AMS 5]
theorem erdos_1019 :
    answer(True) ↔
    ∀ n : ℕ, n ≥ 4 →
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card ≥ n ^ 2 / 4 + (n + 1) / 2 →
        ∃ (k : ℕ) (_ : k > 3) (H : SimpleGraph (Fin k))
          (dH : DecidableRel H.Adj) (f : Fin k → Fin n),
          haveI := dH;
          Function.Injective f ∧
          (IsPlanar H ∧ H.edgeFinset.card = 3 * k - 6) ∧
          ∀ u v, H.Adj u v → G.Adj (f u) (f v) := by
  sorry

/--
Erdős [Er69c] proved that every graph on $n$ vertices with at least
$\lfloor n^2/4 \rfloor + k$ edges (for $k \geq 1$) contains a saturated planar graph on
$\gg k/n$ vertices, answering a question of Dirac.

The bound "$m \gg k/n$" on the number $m$ of vertices of the saturated planar subgraph
is encoded as $k \leq C \cdot m \cdot n$ for an absolute constant $C > 0$, i.e.
$m \geq k/(Cn)$. Saturated planar graphs on $m = 3$ vertices (triangles) are allowed
here; by Turán's theorem a triangle is present as soon as $k \geq 1$, which covers the
degenerate small cases (for $k = 0$ the complete bipartite graph shows the conclusion
would fail, hence the hypothesis $1 \leq k$).
-/
@[category research solved, AMS 5]
theorem erdos_1019.variants.quantitative :
    ∃ C : ℕ, 0 < C ∧
      ∀ n k : ℕ, 1 ≤ k →
        ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
          haveI := dG;
          G.edgeFinset.card ≥ n ^ 2 / 4 + k →
          ∃ (m : ℕ) (_ : m ≥ 3) (_ : k ≤ C * m * n) (H : SimpleGraph (Fin m))
            (dH : DecidableRel H.Adj) (f : Fin m → Fin n),
            haveI := dH;
            Function.Injective f ∧
            (IsPlanar H ∧ H.edgeFinset.card = 3 * m - 6) ∧
            ∀ u v, H.Adj u v → G.Adj (f u) (f v) := by
  sorry

/--
Erdős [Er71] writes it is "easy to construct" a graph on $n$ vertices with
$\lfloor n^2/4 \rfloor + \lfloor (n-1)/2 \rfloor$ edges (one less than the threshold in
`erdos_1019`) which contains no saturated planar graph with more than $3$ vertices.

No restriction on $n$ is needed: for $n \leq 3$ the required edge count is attainable
($3$ edges for $n = 3$, etc.) and no subgraph on more than $3$ vertices exists, and for
$n \geq 4$ small cases check out (e.g. $n = 4$: $5$ edges cannot contain the $6$-edge
$K_4$; $n = 5$: the Turán graph $K_{2,2,1}$ has $8$ edges and is $K_4$-free, while
$5$-vertex triangulations need $9$ edges).
-/
@[category research solved, AMS 5]
theorem erdos_1019.variants.sharpness :
    ∀ n : ℕ,
      ∃ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card = n ^ 2 / 4 + (n - 1) / 2 ∧
        ¬ ∃ (k : ℕ) (_ : k > 3) (H : SimpleGraph (Fin k))
            (dH : DecidableRel H.Adj) (f : Fin k → Fin n),
            haveI := dH;
            Function.Injective f ∧
            (IsPlanar H ∧ H.edgeFinset.card = 3 * k - 6) ∧
            ∀ u v, H.Adj u v → G.Adj (f u) (f v) := by
  sorry

end Erdos1019
