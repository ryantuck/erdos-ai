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
# Erdős Problem 1076

*Reference:* [erdosproblems.com/1076](https://www.erdosproblems.com/1076)

Let $k \geq 5$ and let $\mathcal{F}_k$ be the family of all 3-uniform hypergraphs with $k$
vertices and $k - 2$ edges. Is it true that $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$?

A question of Brown, Erdős, and Sós [BES73] who proved this is true for $k = 4$,
and that for all $k \geq 4$, $\mathrm{ex}_3(n, \mathcal{F}_k) \asymp_k n^2$.

In [Er74c, p.81] Erdős writes 'the only argument in favour of this conjecture (the
conjecture may easily turn out to be nonsense) is the following theorem': every 3-uniform
hypergraph on $n$ vertices with more than $\frac{1}{3}\binom{n}{2}$ edges contains either
a graph on 5 vertices with 3 edges or a graph on 6 vertices with 4 edges. (This is proved
in [Er74c].)

The asymptotic version was proved independently by Bohman and Warnke [BoWa19]
and Glock, Kühn, Lo, and Osthus [GKLO20]; the problem is solved in the affirmative.

This is related to Problem #207, which is an essentially stronger version; in
particular, for $k$ satisfying the right divisibility conditions, the extremal number is
known exactly. See also Problem #1157 for the general Brown–Erdős–Sós conjecture, of
which this problem is the case $r = 3$, $k = s + 2$.

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., *Some extremal problems on r-graphs*.
New Directions in the Theory of Graphs (1973), 53–63.

[Er74c] Erdős, P., *Extremal problems on graphs and hypergraphs*. (1974), 75–84.

[BoWa19] Bohman, T. and Warnke, L., *Large girth approximate Steiner triple systems*.
J. London Math. Soc. (2) (2019), 895–913.

[GKLO20] Glock, S., Kühn, D., Lo, A., and Osthus, D.,
*On a conjecture of Erdős on locally sparse Steiner triple systems*.
Combinatorica (2020), 363–403.
-/

open Finset

namespace Erdos1076

/-- A 3-uniform hypergraph on $n$ vertices. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph $G$ on $k$ vertices is a subhypergraph of $H$ on $n$ vertices
if there is an injection from $\mathrm{Fin}(k)$ to $\mathrm{Fin}(n)$ mapping every edge of
$G$ to an edge of $H$. -/
def IsSubhypergraph {k n : ℕ} (G : Hypergraph3 k) (H : Hypergraph3 n) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    ∀ e ∈ G.edges, e.image f ∈ H.edges

/-- $\mathcal{F}_k$: the family of all 3-uniform hypergraphs with $k$ vertices and exactly
$k - 2$ edges. -/
def familyF (k : ℕ) : Set (Hypergraph3 k) :=
  {G | G.edges.card = k - 2}

/-- $H$ is $\mathcal{F}_k$-free if it contains no subhypergraph from $\mathcal{F}_k$. -/
def IsFkFree {n : ℕ} (k : ℕ) (H : Hypergraph3 n) : Prop :=
  ∀ G : Hypergraph3 k, G ∈ familyF k → ¬IsSubhypergraph G H

/-- The extremal number $\mathrm{ex}_3(n, \mathcal{F}_k)$: the maximum number of edges in an
$\mathcal{F}_k$-free 3-uniform hypergraph on $n$ vertices. -/
noncomputable def ex3 (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Hypergraph3 n, IsFkFree k H ∧ H.edges.card = m}

/--
Erdős Problem 1076 [BES73]:

Is it true that for all $k \geq 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$?

Answered affirmatively by Bohman–Warnke [BoWa19] and, independently,
Glock–Kühn–Lo–Osthus [GKLO20]; hence `answer(True)`.

The asymptotic is formalized as: for every $\varepsilon > 0$, for sufficiently large $n$,
$(1 - \varepsilon) \cdot n^2 / 6 \leq \mathrm{ex}_3(n, \mathcal{F}_k)
\leq (1 + \varepsilon) \cdot n^2 / 6$.
-/
@[category research solved, AMS 5]
theorem erdos_1076 : answer(True) ↔
    ∀ k : ℕ, k ≥ 5 →
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) ^ 2 / 6) ≤ (ex3 n k : ℝ) ∧
      (ex3 n k : ℝ) ≤ (1 + ε) * ((n : ℝ) ^ 2 / 6) := by
  sorry

/--
The case $k = 4$, proved by Brown, Erdős, and Sós [BES73]:
$\mathrm{ex}_3(n, \mathcal{F}_4) \sim n^2 / 6$. Here $\mathcal{F}_4$-freeness is
equivalent to linearity (no two edges share two vertices), and the extremal objects
are approximate partial Steiner triple systems.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.k_eq_4 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) ^ 2 / 6) ≤ (ex3 n 4 : ℝ) ∧
      (ex3 n 4 : ℝ) ≤ (1 + ε) * ((n : ℝ) ^ 2 / 6) := by
  sorry

/--
Brown, Erdős, and Sós [BES73] proved that for all $k \geq 4$,
$\mathrm{ex}_3(n, \mathcal{F}_k) \asymp_k n^2$: there are constants $c_1, c_2 > 0$
(depending on $k$) with $c_1 n^2 \leq \mathrm{ex}_3(n, \mathcal{F}_k) \leq c_2 n^2$
for all sufficiently large $n$.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.order_of_magnitude :
    ∀ k : ℕ, k ≥ 4 →
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c₁ * (n : ℝ) ^ 2 ≤ (ex3 n k : ℝ) ∧ (ex3 n k : ℝ) ≤ c₂ * (n : ℝ) ^ 2 := by
  sorry

/--
Erdős's supporting theorem for the conjecture [Er74c, p.81]: every 3-uniform hypergraph
on $n \geq 5$ vertices with more than $\frac{1}{3}\binom{n}{2} = \frac{n(n-1)}{6}$ edges
contains either a graph on 5 vertices with 3 edges (a member of $\mathcal{F}_5$) or a
graph on 6 vertices with 4 edges (a member of $\mathcal{F}_6$). The edge hypothesis
$|E(H)| > \frac{1}{3}\binom{n}{2}$ is encoded exactly (without division) as
$n(n-1) < 6\,|E(H)|$.

The hypothesis $n \geq 5$ corrects the source page's literal statement, which fails at
$n = 4$: the hypergraph on vertices $\{1,2,3,4\}$ with edges
$\{1,2,3\}, \{1,2,4\}, \{1,3,4\}$ has $3 > \frac{1}{3}\binom{4}{2} = 2$ edges, yet no
member of $\mathcal{F}_5$ or $\mathcal{F}_6$ can embed into a 4-vertex host. The strict
inequality is sharp at $n = 9$: the Steiner triple system $\mathrm{AG}(2,3)$ is linear
and anti-Pasch, hence contains no member of $\mathcal{F}_5$ or $\mathcal{F}_6$, and has
exactly $12 = \frac{1}{3}\binom{9}{2}$ edges.
-/
@[category research solved, AMS 5]
theorem erdos_1076.variants.supporting_theorem :
    ∀ n : ℕ, n ≥ 5 → ∀ H : Hypergraph3 n,
      n * (n - 1) < 6 * H.edges.card →
      ¬IsFkFree 5 H ∨ ¬IsFkFree 6 H := by
  sorry

end Erdos1076
