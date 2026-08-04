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
# Erdős Problem 1033

*Reference:* [erdosproblems.com/1033](https://www.erdosproblems.com/1033)

Let $h(n)$ be such that every graph on $n$ vertices with more than $n^2/4$ edges
contains a triangle whose vertices have degrees summing to at least $h(n)$.
Estimate $h(n)$. In particular, is it true that
$$h(n) \geq (2(\sqrt{3} - 1) - o(1))n?$$

Erdős and Laskar [ErLa85] proved $2(\sqrt{3} - 1)n \geq h(n) \geq (1+c)n$ for some $c > 0$.
The lower bound was improved to $(21/16)n$ by Fan [Fa88].

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[ErLa85] Erdős, P. and Laskar, R., _A note on the size of a chordal subgraph_.
Congr. Numer. (1985), 81–86.

[Fa88] Fan, G., _Degree sum for a triangle in a graph_.
J. Graph Theory (1988), 249–263.
-/

open Classical SimpleGraph Finset

namespace Erdos1033

/--
**Erdős Problem 1033** [Er93, p.344]:

Is it true that $h(n) \geq (2(\sqrt{3} - 1) - o(1))n$? That is, is it true that for every
$\varepsilon > 0$ there exists $N_0$ such that for all $n \geq N_0$, every graph on
$n$ vertices with more than $n^2/4$ edges contains a triangle whose vertices have
degrees summing to at least $(2(\sqrt{3} - 1) - \varepsilon) \cdot n$?
-/
@[category research open, AMS 5]
theorem erdos_1033 : answer(sorry) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (G.degree u + G.degree v + G.degree w : ℝ) ≥
          (2 * (Real.sqrt 3 - 1) - ε) * (n : ℝ) := by
  sorry

/--
Erdős and Laskar [ErLa85] proved the lower bound $h(n) \geq (1 + c)n$ for some constant
$c > 0$: there are $c > 0$ and $N_0$ such that for all $n \geq N_0$, every graph on $n$
vertices with more than $n^2/4$ edges contains a triangle whose vertices have degrees
summing to at least $(1 + c) \cdot n$.
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.erdos_laskar_lower :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (G.degree u + G.degree v + G.degree w : ℝ) ≥ (1 + c) * (n : ℝ) := by
  sorry

/--
Erdős and Laskar [ErLa85] proved the upper bound $2(\sqrt{3} - 1)n \geq h(n)$, formalized
here in asymptotic form: for every $\varepsilon > 0$ and all sufficiently large $n$ there
is a graph on $n$ vertices with more than $n^2/4$ edges in which every triangle has
degree sum at most $(2(\sqrt{3} - 1) + \varepsilon) \cdot n$.

Note that the literal all-$n$ inequality $2(\sqrt{3} - 1)n \geq h(n)$ fails for small
$n$: for $n = 3$ the only graph with more than $9/4$ edges is $K_3$, whose triangle has
degree sum $6$, so $h(3) = 6 > 2(\sqrt{3} - 1) \cdot 3 \approx 4.39$. The asymptotic form
below is the intended content of the bound.
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.erdos_laskar_upper :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 ∧
      ∀ u v w : Fin n, G.Adj u v → G.Adj v w → G.Adj u w →
        (G.degree u + G.degree v + G.degree w : ℝ) ≤
          (2 * (Real.sqrt 3 - 1) + ε) * (n : ℝ) := by
  sorry

/--
Fan [Fa88] improved the Erdős–Laskar lower bound to $h(n) \geq \frac{21}{16} n$: for all
sufficiently large $n$, every graph on $n$ vertices with more than $n^2/4$ edges contains
a triangle whose vertices have degrees summing to at least $\frac{21}{16} \cdot n$.
-/
@[category research solved, AMS 5]
theorem erdos_1033.variants.fan_lower :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (G.degree u + G.degree v + G.degree w : ℝ) ≥ (21 / 16 : ℝ) * (n : ℝ) := by
  sorry

end Erdos1033
