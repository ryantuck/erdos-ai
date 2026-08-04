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
import FormalConjecturesForMathlib.Geometry.«2d»

/-!
# Erdős Problem 1086

*Reference:* [erdosproblems.com/1086](https://www.erdosproblems.com/1086)

Let $g(n)$ be minimal such that any set of $n$ points in $\mathbb{R}^2$ contains the vertices
of at most $g(n)$ many triangles with the same area. Estimate $g(n)$. Equivalently, how many
triangles of area $1$ can a set of $n$ points in $\mathbb{R}^2$ determine? Erdős and Purdy
attribute this question to Oppenheim.

Erdős and Purdy [ErPu71] proved $n^2 \log \log n \ll g(n) \ll n^{5/2}$ and believed the lower
bound to be closer to the truth. The upper bound has been improved a number of times — by Pach
and Sharir [PaSh92], Dumitrescu, Sharir, and Tóth [DST09], Apfelbaum and Sharir [ApSh10], and
Apfelbaum [Ap13]. The best known upper bound is $g(n) \ll n^{20/9}$ by Raz and Sharir [RaSh17].

Erdős and Purdy also ask a similar question about the higher-dimensional generalisations:
let $g_d^r(n)$ be minimal such that any set of $n$ points in $\mathbb{R}^d$ contains the
vertices of at most $g_d^r(n)$ many $r$-dimensional simplices with the same volume. Known
results: $g_3^2(n) \ll n^{8/3}$ [ErPu71], improved to $g_3^2(n) \ll n^{2.4286}$ [DST09];
$g_6^2(n) \gg n^3$ [ErPu71]; $g_4^2(n) \leq g_5^2(n) \ll n^{3-c}$ for some constant $c > 0$
[Pu74]; and an observation of Oppenheim (using a construction of Lenz) detailed in [ErPu71]
shows $g_{2k+2}^k(n) \geq (1/(k+1)^{k+1} + o(1))n^{k+1}$, which Erdős and Purdy conjecture
is best possible. (These generalisations are not formalized here: they would require
simplex-volume machinery not present in this file.)

Related problems: [#90](https://www.erdosproblems.com/90),
[#755](https://www.erdosproblems.com/755).

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_. Ann. Mat.
Pura Appl. (4) (1975), 99–108. [Problem stated at p. 104.]

[ErPu71] Erdős, P. and Purdy, G., _Some extremal problems in geometry_. J. Combin. Theory
Ser. A (1971), 246–252.

[PaSh92] Pach, J. and Sharir, M., _Repeated angles in the plane and related problems_. J. Combin.
Theory Ser. A (1992), 12–22.

[DST09] Dumitrescu, A., Sharir, M., and Tóth, Cs. D., _Extremal problems on triangle areas in
two and three dimensions_. J. Combin. Theory Ser. A (2009), 1177–1198.

[ApSh10] Apfelbaum, R. and Sharir, M., _An improved bound on the number of unit area triangles_.
Discrete Comput. Geom. (2010), 753–761.

[Ap13] Apfelbaum, R., _Geometric Incidences and Repeated Configurations_. Ph.D. Dissertation,
Tel Aviv University, 2013.

[Pu74] Purdy, G., _Some extremal problems in geometry_. Discrete Math. (1974), 305–315.

[RaSh17] Raz, O. E. and Sharir, M., _The number of unit-area triangles in the plane: theme
and variations_. Combinatorica (2017), 1221–1240.
-/

open EuclideanGeometry

namespace Erdos1086

/-- The number of ordered triples of distinct points from $S \subseteq \mathbb{R}^2$ that form
a nondegenerate triangle with area exactly $A$. Each unordered triangle is counted $6$ times
(once per ordering of its vertices). Collinear triples (signed area $0$) are excluded: they do
not form triangles, and without this exclusion $n$ collinear points would determine
$n(n-1)(n-2) \sim n^3$ ordered zero-area "triangles", falsifying any $O(n^{2+\varepsilon})$
bound at $A = 0$. For $A \leq 0$ the count is $0$. The nondegeneracy condition makes the
pairwise-distinctness conjuncts logically redundant; they are kept for clarity. -/
noncomputable def countTrianglesWithArea (S : Finset ℝ²) (A : ℝ) : ℕ :=
  ((S ×ˢ (S ×ˢ S)).filter (fun (p, q, r) =>
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      triangle_area p q r ≠ 0 ∧ |triangle_area p q r| = A)).card

/--
Erdős Problem 1086 (Erdős–Purdy conjecture on equal-area triangles) [ErPu71]:

For every $\varepsilon > 0$, there exists $C > 0$ such that for every finite set $S$ of
points in $\mathbb{R}^2$ and every area $A$, the number of nondegenerate triangles with
area $A$ determined by $S$ is at most $C \cdot |S|^{2+\varepsilon}$.

This formalizes the belief of Erdős and Purdy that $g(n) \ll n^{2+\varepsilon}$,
where $g(n)$ is the maximum number of triangles of the same area in any
set of $n$ points. The statement uses ordered triples, so the constant $C$
absorbs the factor of $6$.
-/
@[category research open, AMS 5 52]
theorem erdos_1086 :
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset ℝ²) (A : ℝ),
      (countTrianglesWithArea S A : ℝ) ≤ C * (S.card : ℝ) ^ (2 + ε) := by
  sorry

/--
The best known upper bound for Erdős Problem 1086, due to Raz and Sharir [RaSh17]:
the number of nondegenerate triangles with any given area determined by a finite set $S$
of points in $\mathbb{R}^2$ is $\ll |S|^{20/9}$. The statement uses ordered triples,
so the constant $C$ absorbs the factor of $6$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1086.variants.raz_sharir_upper_bound :
    ∃ C : ℝ, 0 < C ∧
    ∀ (S : Finset ℝ²) (A : ℝ),
      (countTrianglesWithArea S A : ℝ) ≤ C * (S.card : ℝ) ^ ((20 : ℝ) / 9) := by
  sorry

end Erdos1086
