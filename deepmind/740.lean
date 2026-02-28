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
# Erdős Problem 740

*Reference:* [erdosproblems.com/740](https://www.erdosproblems.com/740)

A question of Erdős and Hajnal [Er69b][Er71, p.100][Er81][Er95d].

Let $\mathfrak{m}$ be an infinite cardinal and $G$ be a graph with chromatic number
$\mathfrak{m}$. Let $r \geq 1$. Must $G$ contain a subgraph of chromatic number
$\mathfrak{m}$ which does not contain any odd cycle of length $\leq r$?

Rödl proved this is true if $\mathfrak{m} = \aleph_0$ and $r = 3$ (see [108] for
the finitary version).

More generally, Erdős and Hajnal asked whether for every cardinal $\mathfrak{m}$ and
integer $r$, there exists $f_r(\mathfrak{m})$ such that every graph with chromatic
number $\geq f_r(\mathfrak{m})$ contains a subgraph with chromatic number
$\mathfrak{m}$ with no odd cycle of length $\leq r$.
-/

open SimpleGraph Cardinal

universe u

namespace Erdos740

/-- The cardinal chromatic number of a graph: the infimum of cardinals $\kappa$
for which $G$ admits a proper $\kappa$-coloring. -/
noncomputable def cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem 740 [Er69b][Er71][Er81][Er95d]:

If $G$ is a graph with infinite chromatic number $\mathfrak{m}$, then for every
$r \geq 1$, $G$ contains a subgraph with chromatic number $\mathfrak{m}$ that has
no odd cycle of length $\leq r$.

A question of Erdős and Hajnal. Rödl proved the case
$\mathfrak{m} = \aleph_0$, $r = 3$.
-/
@[category research open, AMS 5]
theorem erdos_740 {V : Type u} (G : SimpleGraph V)
    (𝔪 : Cardinal.{u}) (h𝔪_inf : ℵ₀ ≤ 𝔪)
    (hχ : cardChromaticNumber G = 𝔪) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (W : Type u) (H : SimpleGraph W),
      cardChromaticNumber H = 𝔪 ∧
      (∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b)) ∧
      (∀ (w : W) (p : H.Walk w w), p.IsCycle → Odd p.length → r < p.length) := by
  sorry

end Erdos740
