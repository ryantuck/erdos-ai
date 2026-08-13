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
# Erdős Problem 1009

*Reference:* [erdosproblems.com/1009](https://www.erdosproblems.com/1009)

Is it true that, for every $c > 0$, there exists $f(c)$ such that every graph on $n$
vertices with at least $\lfloor n^2/4 \rfloor + k$ edges, where $k < cn$, contains at least
$k - f(c)$ many edge-disjoint triangles?

Erdős proved this for $c < 1/2$ (indeed with $f(c) = 0$), using a theorem of Erdős and
Gallai: every graph on $n$ vertices with at least $(n-1)^2/4 + 2$ edges and chromatic
number $3$ contains a triangle. At first Erdős thought $f(c) = 0$ for larger values of
$c$, but this is false: an example of Sauer proves that $f(2) \geq 1$. Sauer's example is
a graph on $n = 2r + 4$ vertices with $\lfloor n^2/4 \rfloor + 2n - 6$ edges — the
complete tripartite graph on $[r] \times [r] \times [4]$ with a $K_4$ added on the $[4]$
part — which contains only $2n - 7$ edge-disjoint triangles.

The question was answered affirmatively by Győri [Gy88], who showed $f(c) \ll c^2$, and
also that $f(c) = 0$ if $c < 2$ for odd $n$ or $c < 3/2$ for even $n$.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97-109.

[Gy88] Győri, E., _On the number of edge disjoint triangles in graphs of given size_
(1988).
-/

open SimpleGraph

namespace Erdos1009

/-- A graph `G` on `n` vertices contains a collection of `t` edge-disjoint triangles. -/
def HasEdgeDisjointTriangles {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  ∃ (tri : Fin t → Fin 3 → Fin n),
    (∀ i, Function.Injective (tri i)) ∧
    (∀ i (j k : Fin 3), j ≠ k → G.Adj (tri i j) (tri i k)) ∧
    (∀ i₁ i₂, i₁ ≠ i₂ →
      ∀ (j₁ k₁ : Fin 3), j₁ ≠ k₁ →
      ∀ (j₂ k₂ : Fin 3), j₂ ≠ k₂ →
        ¬((tri i₁ j₁ = tri i₂ j₂ ∧ tri i₁ k₁ = tri i₂ k₂) ∨
          (tri i₁ j₁ = tri i₂ k₂ ∧ tri i₁ k₁ = tri i₂ j₂)))

/--
Erdős Problem 1009 [Er71, p.98]:

For every $c > 0$, there exists $f(c)$ such that every graph on $n$ vertices with at
least $\lfloor n^2/4 \rfloor + k$ edges, where $k < cn$, contains at least $k - f(c)$
many edge-disjoint triangles. Proved by Győri [Gy88].
-/
@[category research solved, AMS 5]
theorem erdos_1009 : answer(True) ↔
    ∀ c : ℝ, c > 0 →
    ∃ f : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∀ k : ℕ, (k : ℝ) < c * (n : ℝ) →
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    HasEdgeDisjointTriangles G (k - f) := by sorry

/--
Erdős [Er71] proved the result with $f(c) = 0$ for $c < 1/2$: every graph on $n$
vertices with at least $\lfloor n^2/4 \rfloor + k$ edges, where $k < cn$ and
$0 < c < 1/2$, contains $k$ edge-disjoint triangles.
-/
@[category research solved, AMS 5]
theorem erdos_1009.variants.erdos_small_c :
    ∀ c : ℝ, 0 < c → c < 1 / 2 →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∀ k : ℕ, (k : ℝ) < c * (n : ℝ) →
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    HasEdgeDisjointTriangles G k := by sorry

/--
Sauer's example proves that $f(2) \geq 1$: taking $f = 0$ fails for $c = 2$. His
witness is a graph on $n = 2r + 4$ vertices with $\lfloor n^2/4 \rfloor + 2n - 6$
edges (the complete tripartite graph on $[r] \times [r] \times [4]$ with a $K_4$ on
the $[4]$ part) containing only $2n - 7$ edge-disjoint triangles.
-/
@[category research solved, AMS 5]
theorem erdos_1009.variants.sauer_f_two :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∀ k : ℕ, k < 2 * n →
      G.edgeFinset.card ≥ n ^ 2 / 4 + k →
      HasEdgeDisjointTriangles G k) := by sorry

/--
Győri [Gy88] proved the result with $f(c) \ll c^2$: there is an absolute constant
$C > 0$ such that for every $c > 0$ some $f \leq C c^2$ works.
-/
@[category research solved, AMS 5]
theorem erdos_1009.variants.gyori_quadratic :
    ∃ C : ℝ, C > 0 ∧
    ∀ c : ℝ, c > 0 →
    ∃ f : ℕ, (f : ℝ) ≤ C * c ^ 2 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∀ k : ℕ, (k : ℝ) < c * (n : ℝ) →
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    HasEdgeDisjointTriangles G (k - f) := by sorry

/--
Győri [Gy88] also proved that $f(c) = 0$ if $c < 2$ for odd $n$, or $c < 3/2$ for
even $n$. Since $k < cn$ for some $c < 2$ iff $k < 2n$, and $k < cn$ for some
$c < 3/2$ iff $2k < 3n$, this is stated with the equivalent integer inequalities.
-/
@[category research solved, AMS 5]
theorem erdos_1009.variants.gyori_f_eq_zero :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∀ k : ℕ,
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    ((Odd n ∧ k < 2 * n) ∨ (Even n ∧ 2 * k < 3 * n)) →
    HasEdgeDisjointTriangles G k := by sorry

end Erdos1009
