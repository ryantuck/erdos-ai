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
# Erdős Problem 1019

*Reference:* [erdosproblems.com/1019](https://www.erdosproblems.com/1019)

[Er64f] [Er69c] [Er71]
-/

open SimpleGraph Finset

namespace Erdos1019

/-- A simple graph is planar if it admits a topological embedding into the
    plane without edge crossings. Defined abstractly here. -/
def IsPlanar {V : Type*} (_ : SimpleGraph V) : Prop := sorry

/--
Erdős Problem 1019 [Er64f, Er69c, Er71]:

Every graph on $n \geq 4$ vertices with at least
$\lfloor n^2/4 \rfloor + \lfloor (n+1)/2 \rfloor$ edges contains a maximal planar subgraph
(planar with exactly $3k - 6$ edges) on some $k > 3$ vertices.

Proved by Simonovits.
-/
@[category research solved, AMS 5]
theorem erdos_1019 :
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

end Erdos1019
