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
# Erdős Problem 1034

A conjecture of Erdős and Faudree, and a stronger version of Problem #905.
Erdős asked whether every dense graph (with more than $n^2/4$ edges) contains a triangle
$T$ together with more than $(1/2 - o(1))n$ vertices each adjacent to at least two of the
vertices of $T$.

Erdős [Er93] says "perhaps this conjecture is a bit too optimistic", and in general asks
how large the number of such vertices can be, and suggested the answer is different if
$G$ has no $K_4$.

The conjecture was disproved by Ma and Tang (see their note at
[staff.ustc.edu.cn/~jiema/Erdos-1034.pdf](http://staff.ustc.edu.cn/~jiema/Erdos-1034.pdf));
erdosproblems.com marks the status DISPROVED (LEAN), i.e. "solved in the negative and the
proof verified in Lean". More generally, Erdős and Faudree asked about the threshold
$h(n)$ such that every graph with $n$ vertices and $> n^2/4$ edges contains a triangle
and $h(n)$ other vertices which are connected to at least two vertices of the triangle.
The Ma–Tang construction, combined with the fact that every graph with $> n^2/4$ edges
contains a book of size $n/6$ (cf. Problem #905), shows
$$(1/6 - o(1))n \le h(n) \le (2 - \sqrt{5/2} + o(1))n.$$
Ma and Tang also sketch a proof that the conjecture remains false for $K_4$-free graphs,
where their construction gives the bound $(2\sqrt{3} - 3 + o(1))n$
($2\sqrt{3} - 3 \approx 0.464$).

*Reference:* [erdosproblems.com/1034](https://www.erdosproblems.com/1034)
(page last edited 28 October 2025, accessed 2026-02-22)

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.
-/

open Classical SimpleGraph Finset

namespace Erdos1034

/-- The number of vertices in a graph adjacent to at least two of three
given vertices $u$, $v$, $w$. -/
noncomputable def adjToAtLeastTwoOfTriangle {n : ℕ} (G : SimpleGraph (Fin n))
    (u v w : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Fin n =>
    (G.Adj x u ∧ G.Adj x v) ∨ (G.Adj x v ∧ G.Adj x w) ∨ (G.Adj x u ∧ G.Adj x w)).card

/--
**Erdős Problem 1034** (Disproved) [Er93, p. 344]:

For every $\varepsilon > 0$, does there exist $N_0$ such that for all $n \ge N_0$, every graph on
$n$ vertices with more than $n^2 / 4$ edges contains a triangle $\{u, v, w\}$ such that
more than $(1/2 - \varepsilon) \cdot n$ vertices are each adjacent to at least two of $u$, $v$, $w$?

Disproved by Ma and Tang, who construct a graph with $n$ vertices and
$> n^2 / 4$ edges in which every triangle has at most $(2 - \sqrt{5/2} + o(1))n$
vertices adjacent to at least two of its vertices ($2 - \sqrt{5/2} \approx 0.4189$).
-/
@[category research solved, AMS 5]
theorem erdos_1034 : answer(False) ↔
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (adjToAtLeastTwoOfTriangle G u v w : ℝ) > (1 / 2 - ε) * (n : ℝ) := by
  sorry

/--
Lower bound for Erdős Problem 1034 [Er93, p. 344]:

For every $\varepsilon > 0$ and all sufficiently large $n$, every graph on $n$ vertices
with more than $n^2 / 4$ edges contains a triangle $\{u, v, w\}$ such that more than
$(1/6 - \varepsilon) \cdot n$ vertices are each adjacent to at least two of $u$, $v$, $w$.

This follows from the fact that every graph with more than $n^2/4$ edges contains a book
of size $n/6$, i.e. an edge lying in at least $n/6$ triangles (cf. Problem #905): the two
endpoints of such an edge together with any one page form a triangle, and every other
page is adjacent to both endpoints. Equivalently, $h(n) \ge (1/6 - o(1))n$ for the
Erdős–Faudree threshold $h(n)$.
-/
@[category research solved, AMS 5]
theorem erdos_1034.variants.book_lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 →
      ∃ u v w : Fin n, G.Adj u v ∧ G.Adj v w ∧ G.Adj u w ∧
        (adjToAtLeastTwoOfTriangle G u v w : ℝ) > (1 / 6 - ε) * (n : ℝ) := by
  sorry

/--
The Ma–Tang construction disproving Erdős Problem 1034:

For every $\varepsilon > 0$ and all sufficiently large $n$, there is a graph on $n$
vertices with more than $n^2 / 4$ edges in which every triangle $\{u, v, w\}$ has at most
$(2 - \sqrt{5/2} + \varepsilon) \cdot n$ vertices adjacent to at least two of
$u$, $v$, $w$. Since $2 - \sqrt{5/2} \approx 0.4189 < 1/2$, this refutes the conjecture
`erdos_1034` and shows $h(n) \le (2 - \sqrt{5/2} + o(1))n$.

See the note of Ma and Tang at
[staff.ustc.edu.cn/~jiema/Erdos-1034.pdf](http://staff.ustc.edu.cn/~jiema/Erdos-1034.pdf).
-/
@[category research solved, AMS 5]
theorem erdos_1034.variants.ma_tang_construction :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ G : SimpleGraph (Fin n),
      G.edgeFinset.card > n ^ 2 / 4 ∧
      ∀ u v w : Fin n, G.Adj u v → G.Adj v w → G.Adj u w →
        (adjToAtLeastTwoOfTriangle G u v w : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ) := by
  sorry

end Erdos1034
