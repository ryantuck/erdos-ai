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
# Erdős Problem 739

*Reference:* [erdosproblems.com/739](https://www.erdosproblems.com/739)

A question of Galvin [Ga73], who proved the case $\mathfrak{m} = \aleph_0$.
Komjáth [Ko88b] proved it is consistent that the answer is no
(with $\mathfrak{m} = \aleph_2$ and $\mathfrak{n} = \aleph_1$).
Shelah [Sh90] proved that assuming $V = L$, the answer is yes
with $\mathfrak{m} = \aleph_2$ and $\mathfrak{n} = \aleph_1$.

[Er81] Erdős, P., 1981.

[Ga73] Galvin, F., 1973.

[Ko88b] Komjáth, P., 1988.

[Sh90] Shelah, S., 1990.
-/

open SimpleGraph Cardinal

universe u

namespace Erdos739

/-- The cardinal chromatic number of a graph: the infimum of cardinals $\kappa$
for which $G$ admits a proper $\kappa$-coloring. -/
noncomputable def cardChromaticNumber {V : Type u}
    (G : SimpleGraph V) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ (α : Type u), #α = κ ∧ Nonempty (G.Coloring α)}

/--
Erdős Problem 739 [Er81]:

If $G$ is a graph with infinite chromatic number $\mathfrak{m}$, then for every infinite
cardinal $\mathfrak{n} < \mathfrak{m}$, there is a subgraph of $G$ with chromatic
number $\mathfrak{n}$.

A question of Galvin [Ga73], who proved the case $\mathfrak{m} = \aleph_0$. This is not provable
in ZFC: Komjáth [Ko88b] showed it is consistent that the answer is no.
-/
@[category research open, AMS 5 3]
theorem erdos_739 : answer(sorry) ↔
    ∀ {V : Type u} (G : SimpleGraph V)
    (𝔪 : Cardinal.{u}), ℵ₀ ≤ 𝔪 → cardChromaticNumber G = 𝔪 →
    ∀ (𝔫 : Cardinal.{u}), ℵ₀ ≤ 𝔫 → 𝔫 < 𝔪 →
    ∃ (W : Type u) (H : SimpleGraph W),
      cardChromaticNumber H = 𝔫 ∧
      ∃ f : W → V, Function.Injective f ∧ ∀ a b, H.Adj a b → G.Adj (f a) (f b) := by
  sorry

end Erdos739
