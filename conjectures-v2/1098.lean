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
# Erdős Problem 1098

Let $G$ be a group and $\Gamma = \Gamma(G)$ be the non-commuting graph, with vertices the
elements of $G$ and an edge between $g$ and $h$ if and only if $g$ and $h$ do not commute,
$gh \neq hg$. If $\Gamma$ contains no infinite complete subgraph, then is there a finite
bound on the size of complete subgraphs of $\Gamma$?

Solved in the affirmative by Neumann [Ne76], who proved that $\Gamma$ contains no infinite
complete subgraph if and only if the centre of $G$ has finite index, and noted that if the
centre has index $n$ then $\Gamma$ contains no complete subgraph on more than $n$ vertices.
Neumann reported the problem was asked by Erdős at the 15th Summer Research Institute of
the Australian Mathematical Society in 1975.

*Reference:* [erdosproblems.com/1098](https://www.erdosproblems.com/1098)

[Ne76] Neumann, B.H., _A problem of Paul Erdős on groups_, J. Austral. Math. Soc. Ser. A
21 (1976), 467-472.

See also: Erdős Problem 117 (pairwise non-commuting elements and covers by abelian
subgroups).
-/

open SimpleGraph

namespace Erdos1098

/-- The non-commuting graph of a group $G$ has vertices the elements of $G$,
with an edge between $g$ and $h$ if and only if they do not commute ($gh \neq hg$). -/
def nonCommutingGraph (G : Type*) [Group G] : SimpleGraph G where
  Adj g h := g * h ≠ h * g
  symm := by intro _ _ hab; exact Ne.symm hab
  loopless := by intro a hab; exact hab rfl

/--
Erdős Problem 1098 (solved affirmatively by Neumann [Ne76]):
Let $G$ be a group and $\Gamma(G)$ be the non-commuting graph, with vertices the elements
of $G$ and an edge between $g$ and $h$ if and only if $gh \neq hg$. If $\Gamma$ contains no
infinite complete subgraph (i.e., no infinite set of pairwise non-commuting elements),
then is there a finite bound on the size of complete subgraphs of $\Gamma$?

Neumann proved the answer is yes: $\Gamma$ contains no infinite complete subgraph if and
only if the centre of $G$ has finite index (see
`erdos_1098.variants.center_finite_index`), and if the centre has index $n$ then $\Gamma$
contains no complete subgraph on more than $n$ vertices (see
`erdos_1098.variants.index_bound`).
-/
@[category research solved, AMS 5 20]
theorem erdos_1098 : answer(True) ↔
    ∀ (G : Type*) [Group G],
      (¬ ∃ S : Set G, S.Infinite ∧ (nonCommutingGraph G).IsClique S) →
      ∃ n : ℕ, ∀ S : Finset G, (nonCommutingGraph G).IsClique (S : Set G) → S.card ≤ n := by
  sorry

/--
Variant of Erdős Problem 1098 — Neumann's characterization [Ne76]:
the non-commuting graph of a group $G$ contains no infinite complete subgraph (no
infinite set of pairwise non-commuting elements) if and only if the centre of $G$ has
finite index.
-/
@[category research solved, AMS 5 20]
theorem erdos_1098.variants.center_finite_index (G : Type*) [Group G] :
    (¬ ∃ S : Set G, S.Infinite ∧ (nonCommutingGraph G).IsClique S) ↔
    (Subgroup.center G).FiniteIndex := by
  sorry

/--
Variant of Erdős Problem 1098 — Neumann's quantitative bound [Ne76]: if the centre of $G$
has finite index $n$, then the non-commuting graph of $G$ contains no complete subgraph
on more than $n$ vertices (pairwise non-commuting elements lie in pairwise distinct
cosets of the centre).
-/
@[category research solved, AMS 5 20]
theorem erdos_1098.variants.index_bound (G : Type*) [Group G] (n : ℕ)
    (hn : (Subgroup.center G).index = n) (hn0 : n ≠ 0) :
    ∀ S : Finset G, (nonCommutingGraph G).IsClique (S : Set G) → S.card ≤ n := by
  sorry

end Erdos1098
