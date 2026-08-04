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
# Erdős Problem 1089

*Reference:* [erdosproblems.com/1089](https://www.erdosproblems.com/1089)

Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$
determines at least $n$ many distinct distances. Estimate $g_d(n)$. In particular, does
$\lim_{d \to \infty} g_d(n) / d^{n-1}$ exist?

A question of Kelly, appearing in [Er75f, p.105]. SOLVED: for $n \geq 2$,
$\binom{d+1}{n-1} + 1 \leq g_d(n) \leq \binom{d+n-1}{n-1} + 1$, the lower bound due to
Aletheia [Fe26] (a generalisation of the construction in problem 502) and the upper bound
due to Bannai, Bannai, and Stanton [BBS83]; whence, for $n \geq 2$, the limit exists and
equals $1/(n-1)!$.

Erdős [Er75f] writes it is 'easy' to see that $g_d(n) \gg d^{n-1}$, and Erdős and Straus
proved (in unpublished work mentioned in [Er75f]) that $g_d(n) \leq c^{d^{1-b_n}}$ for some
constants $c > 0$ and $b_n > 0$. It is trivial that $g_1(3) = 4$, and easy to see that
$g_2(3) = 6$; Croft [Cr62] proved $g_3(3) = 7$. The vertices of a $d$-dimensional cube
demonstrate that $g_d(d+1) > 2^d$. The function $g_d(n)$ is essentially the inverse of the
function $f_d(n)$ considered in problem 1083: $g_d(n) > m$ if and only if $f_d(m) < n$. The
behaviour of $g_d(3)$ is the focus of problem 502.

[BBS83] Bannai, E., Bannai, E., and Stanton, D., _An upper bound for the cardinality of an
$s$-distance subset in real Euclidean space. II_. Combinatorica (1983), 147–152.

[Cr62] Croft, H. T., _9-point and 7-point configurations in 3-space_.
Proc. London Math. Soc. (3) (1962), 400-424.

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Ann. Mat. Pura Appl. (4) (1975), 99-108.

[Fe26] T. Feng et al, _Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on the
Erdős Problems_. arXiv:2601.22401 (2026).
-/

open Classical Finset Filter

namespace Erdos1089

/-- The set of distinct distances determined by a finite set of points
in $d$-dimensional Euclidean space. -/
noncomputable def distinctDistances {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : Finset ℝ :=
  S.offDiag.image (fun pq => dist pq.1 pq.2)

/-- The number of distinct distances determined by a finite set of points. -/
noncomputable def distinctDistanceCount {d : ℕ} (S : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  (distinctDistances S).card

/-- $g_d(n)$ is the minimal number of points in $\mathbb{R}^d$ such that any collection of
that many points determines at least $n$ distinct distances. -/
noncomputable def g (d n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (S : Finset (EuclideanSpace ℝ (Fin d))), S.card ≥ m →
    distinctDistanceCount S ≥ n}

/--
Erdős Problem 1089 (Kelly's question, resolved):
Let $g_d(n)$ be minimal such that every collection of $g_d(n)$ points in $\mathbb{R}^d$ determines
at least $n$ distinct distances. Does $\lim_{d \to \infty} g_d(n) / d^{n-1}$ exist? Yes: the
limit exists and equals $1/(n-1)!$ for all $n \geq 2$.

The lower bound $\binom{d+1}{n-1} + 1 \leq g_d(n)$ is due to Aletheia [Fe26]
and the upper bound $g_d(n) \leq \binom{d+n-1}{n-1} + 1$ is due to Bannai, Bannai,
and Stanton [BBS83].
-/
@[category research solved, AMS 5 52]
theorem erdos_1089 :
    answer(True) ↔
      ∀ (n : ℕ), 2 ≤ n →
        Tendsto (fun d : ℕ => (g d n : ℝ) / (d : ℝ) ^ (n - 1))
          atTop (nhds (1 / (Nat.factorial (n - 1) : ℝ))) := by
  sorry

/-- The lower bound $\binom{d+1}{n-1} + 1 \leq g_d(n)$ for $n \geq 2$, due to
Aletheia [Fe26] (a generalisation of the construction in problem 502). -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.lower_bound (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    Nat.choose (d + 1) (n - 1) + 1 ≤ g d n := by
  sorry

/-- The upper bound $g_d(n) \leq \binom{d+n-1}{n-1} + 1$ for $n \geq 2$, due to
Bannai, Bannai, and Stanton [BBS83]. -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.upper_bound (n : ℕ) (hn : 2 ≤ n) (d : ℕ) :
    g d n ≤ Nat.choose (d + n - 1) (n - 1) + 1 := by
  sorry

/-- $g_1(3) = 4$: four points on a line always determine at least three distinct
distances, and three points need not. Described as trivial on the problem page. -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.g1_3 : g 1 3 = 4 := by
  sorry

/-- $g_2(3) = 6$: six points in the plane always determine at least three distinct
distances, and five points need not (e.g. the vertices of a regular pentagon).
Described as easy on the problem page. -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.g2_3 : g 2 3 = 6 := by
  sorry

/-- $g_3(3) = 7$: seven points in $\mathbb{R}^3$ always determine at least three distinct
distances, and six points need not (e.g. the vertices of a regular octahedron).
Due to Croft [Cr62]. -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.g3_3 : g 3 3 = 7 := by
  sorry

/-- $g_d(d+1) > 2^d$: the vertices of a $d$-dimensional cube form $2^d$ points
determining only $d$ distinct distances. -/
@[category research solved, AMS 5 52]
theorem erdos_1089.variants.hypercube (d : ℕ) : 2 ^ d < g d (d + 1) := by
  sorry

end Erdos1089
