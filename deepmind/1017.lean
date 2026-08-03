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

import FormalConjectures.Util.ProblemImports

/-!
# Erdős Problem 1017

*Reference:* [erdosproblems.com/1017](https://www.erdosproblems.com/1017)

Let $f(n,k)$ be such that every graph on $n$ vertices and $k$ edges can be
partitioned into at most $f(n,k)$ edge-disjoint complete graphs. Estimate
$f(n,k)$ for $k > n^2/4$.

The function $f(n,k)$ is sometimes called the clique partition number.

Erdős, Goodman, and Pósa [EGP66] proved that $f(n,k) \le \lfloor n^2/4 \rfloor$ for all $k$
(and in fact edges and triangles suffice), which is best possible in general,
as witnessed by a complete bipartite graph. Erdős [Er71] asks whether this
bound can be sharpened when $k > n^2/4$. The problem is listed as OPEN on
erdosproblems.com (page last edited 28 December 2025).

Lovász [Lo68] proved that every graph on $n$ vertices and $k$ edges can be expressed
as a union of $\binom{n}{2} - k + t$ complete graphs, where $t$ is maximal such that
$t^2 - t \le \binom{n}{2} - k$, without the requirement that the complete graphs be
edge-disjoint. Lovász's result is sharp in many cases.

If $k > n^2/4$ and the graph contains no $K_4$, the problem is equivalent to finding
the minimum number of edge-disjoint triangles; this special case was also asked about
by Erdős. A complete answer was provided by Győri and Keszegh [GyKe17], who proved
that every $K_4$-free graph with $n$ vertices and $\lfloor n^2/4 \rfloor + m$ edges
contains $m$ pairwise edge-disjoint triangles.

See also [erdosproblems.com/184](https://www.erdosproblems.com/184) for an analogous
problem decomposing into edges and cycles, and
[erdosproblems.com/583](https://www.erdosproblems.com/583) for decomposing into paths.
The clique partition problem for chordal graphs is the subject of
[erdosproblems.com/81](https://www.erdosproblems.com/81).

[EGP66] Erdős, P., Goodman, A. W., and Pósa, L., _The representation of a graph by set
intersections_. Canadian Journal of Mathematics 18 (1966), 106-112.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[Lo68] Lovász, L., _On covering of graphs_. Theory of Graphs (Proc. Colloq., Tihany, 1966)
(1968), 231-236.

[GyKe17] Győri, E. and Keszegh, B., _On the number of edge-disjoint triangles in K₄-free
graphs_. Combinatorica **37** (2017), 1113-1124.
-/

open SimpleGraph Finset Filter

namespace Erdos1017

/--
Erdős Problem 1017 [Er71]:

Erdős asks whether the clique partition number $f(n,k)$ can be improved
below $\lfloor n^2/4 \rfloor$ when the number of edges $k$ exceeds $n^2/4$,
here formalized for all sufficiently large $n$.
-/
@[category research open, AMS 5]
theorem erdos_1017 : answer(sorry) ↔
    ∀ᶠ n in atTop,
      ∀ (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
        haveI := dG;
        G.edgeFinset.card > n ^ 2 / 4 →
          ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
            k < n ^ 2 / 4 ∧
            (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
            (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
            (∀ i : Fin k, ∃ (S : Finset (Fin n)),
              G.IsClique (↑S : Set (Fin n)) ∧
              parts i = S.offDiag.image (Quot.mk _)) := by
  sorry

/--
Erdős–Goodman–Pósa theorem [EGP66]:

Every simple graph on $n$ vertices can be decomposed into at most
$\lfloor n^2/4 \rfloor$ edge-disjoint complete subgraphs.
-/
@[category research solved, AMS 5]
theorem erdos_1017.variants.erdos_goodman_posa :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
        k ≤ n ^ 2 / 4 ∧
        (∀ i j : Fin k, i ≠ j → Disjoint (parts i) (parts j)) ∧
        (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
        (∀ i : Fin k, ∃ (S : Finset (Fin n)),
          G.IsClique (↑S : Set (Fin n)) ∧
          parts i = S.offDiag.image (Quot.mk _)) := by
  sorry

/--
Győri–Keszegh theorem [GyKe17]:

Every $K_4$-free graph on $n$ vertices with $\lfloor n^2/4 \rfloor + m$ edges contains
$m$ pairwise edge-disjoint triangles. This completely answers the $K_4$-free special
case of Erdős Problem 1017, which is equivalent to finding the minimum number of
edge-disjoint triangles.
-/
@[category research solved, AMS 5]
theorem erdos_1017.variants.gyori_keszegh :
    ∀ (n m : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      (∀ S : Finset (Fin n), S.card = 4 → ¬ G.IsClique (↑S : Set (Fin n))) →
      G.edgeFinset.card = n ^ 2 / 4 + m →
      ∃ (tris : Fin m → Finset (Sym2 (Fin n))),
        (∀ i j : Fin m, i ≠ j → Disjoint (tris i) (tris j)) ∧
        (∀ i : Fin m, ∃ (S : Finset (Fin n)),
          S.card = 3 ∧ G.IsClique (↑S : Set (Fin n)) ∧
          tris i = S.offDiag.image (Quot.mk _)) := by
  sorry

/--
Lovász's theorem [Lo68]:

Every graph on $n$ vertices and $k$ edges is the union of at most
$\binom{n}{2} - k + t$ complete graphs, where $t$ is maximal such that
$t^2 - t \le \binom{n}{2} - k$, without the requirement that the complete graphs be
edge-disjoint (coverage replaces the disjointness condition of the main statement).

The natural-number subtractions are safe: $k \le \binom{n}{2}$ for every simple
graph on $n$ vertices, and $t \le t^2$ for every $t \in \mathbb{N}$.
-/
@[category research solved, AMS 5]
theorem erdos_1017.variants.lovasz :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (dG : DecidableRel G.Adj),
      haveI := dG;
      ∀ t : ℕ,
        (t ^ 2 - t ≤ n.choose 2 - G.edgeFinset.card ∧
          ∀ s : ℕ, s ^ 2 - s ≤ n.choose 2 - G.edgeFinset.card → s ≤ t) →
        ∃ (k : ℕ) (parts : Fin k → Finset (Sym2 (Fin n))),
          k ≤ n.choose 2 - G.edgeFinset.card + t ∧
          (∀ e, e ∈ G.edgeFinset ↔ ∃ i, e ∈ parts i) ∧
          (∀ i : Fin k, ∃ (S : Finset (Fin n)),
            G.IsClique (↑S : Set (Fin n)) ∧
            parts i = S.offDiag.image (Quot.mk _)) := by
  sorry

end Erdos1017
