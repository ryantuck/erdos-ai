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
# Erdős Problem 1007

*Reference:* [erdosproblems.com/1007](https://www.erdosproblems.com/1007)

The dimension of a graph $G$ is the minimal $n$ such that $G$ can be embedded in
$\mathbb{R}^n$ such that every edge of $G$ is a unit line segment. (Following
Erdős–Harary–Tutte, the embedding must send distinct vertices to distinct points and
adjacent vertices to points at Euclidean distance exactly $1$; non-adjacent vertices are
unconstrained, and may in particular also lie at unit distance.) This notion was defined
by Erdős, Harary, and Tutte. The problem was posed by Erdős to Soifer in January 1992.

What is the smallest number of edges in a graph with dimension $4$?

The answer is $9$, achieved solely by $K_{3,3}$, proved by House [Ho13]. An alternative
proof was given by Chaffee and Noble [ChNo16], who also prove that the smallest number
of edges in a graph of dimension $5$ is $15$ (achieved by $K_6$ and $K_{1,3,3}$).

As of the source page (accessed 2026-02-22), erdosproblems.com marks this problem
SOLVED (LEAN): resolved, with the resolution verified in Lean.

[So09e] Soifer, A., *The Mathematical Coloring Book*, Springer, 2009.

[Ho13] House, R. F., *A 4-dimensional graph has at least 9 edges*.
Discrete Mathematics **313** (2013), 1783–1789.

[ChNo16] Chaffee, J. and Noble, M., *Dimension 4 and dimension 5 graphs with
minimum edge set*. Australasian Journal of Combinatorics **64** (2016), 327–333.
-/

open SimpleGraph

namespace Erdos1007

/-- A unit-distance representation of a simple graph $G$ in $\mathbb{R}^n$, in the sense of
Erdős–Harary–Tutte: an injective map from vertices to Euclidean $n$-space sending
adjacent vertices to points at distance exactly $1$. Non-adjacent vertices are
unconstrained — they may also lie at unit distance. Injectivity is essential: without
it, e.g., each side of $K_{3,3}$ could collapse to a single point, since vertices on the
same side are non-adjacent twins. -/
def IsUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (f : V → EuclideanSpace ℝ (Fin n)) : Prop :=
  Function.Injective f ∧
  ∀ u v, G.Adj u v → dist (f u) (f v) = 1

/-- A graph admits a unit-distance representation in $\mathbb{R}^n$. Padding with a zero
coordinate turns a representation in $\mathbb{R}^n$ into one in $\mathbb{R}^{n+1}$, so
"$G$ has dimension exactly $4$" is encoded as `HasUnitDistRep G 4 ∧ ¬HasUnitDistRep G 3`. -/
def HasUnitDistRep {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ f : V → EuclideanSpace ℝ (Fin n), IsUnitDistRep G n f

/--
Erdős Problem 1007 [So09e]:

What is the smallest number of edges in a graph with dimension $4$, where the dimension
of a graph is the minimal $n$ for a unit-distance representation in $\mathbb{R}^n$?

The answer is $9$: the set of edge counts of graphs of dimension exactly $4$ has least
element $9$, achieved solely by $K_{3,3}$. Proved by House [Ho13], with an alternative
proof by Chaffee and Noble [ChNo16].
-/
@[category research solved, AMS 5 51]
theorem erdos_1007 :
    -- the set of edge counts of graphs of dimension exactly 4 has least element 9
    IsLeast {m : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      HasUnitDistRep G 4 ∧ ¬HasUnitDistRep G 3 ∧ G.edgeFinset.card = m}
    answer((9 : ℕ)) := by
  sorry

/--
Uniqueness variant of Erdős Problem 1007 [Ho13]:

Any graph of dimension exactly $4$ with exactly $9$ edges is isomorphic to $K_{3,3}$.
-/
@[category research solved, AMS 5 51]
theorem erdos_1007.variants.uniqueness (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h4 : HasUnitDistRep G 4) (h3 : ¬HasUnitDistRep G 3)
    (hedge : G.edgeFinset.card = 9) :
    Nonempty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  sorry

/--
Dimension-5 analogue of Erdős Problem 1007 [ChNo16]:

The smallest number of edges in a graph of dimension exactly $5$ is $15$, achieved by
$K_6$ and $K_{1,3,3}$.
-/
@[category research solved, AMS 5 51]
theorem erdos_1007.variants.dim5 :
    -- the set of edge counts of graphs of dimension exactly 5 has least element 15
    IsLeast {m : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V)
      (_ : DecidableRel G.Adj),
      HasUnitDistRep G 5 ∧ ¬HasUnitDistRep G 4 ∧ G.edgeFinset.card = m}
    (15 : ℕ) := by
  sorry

end Erdos1007
