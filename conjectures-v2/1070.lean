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
# Erdős Problem 1070

*Reference:* [erdosproblems.com/1070](https://www.erdosproblems.com/1070)

Let $f(n)$ be maximal such that, given any $n$ points in $\mathbb{R}^2$, there exist $f(n)$
points such that no two are distance $1$ apart. Estimate $f(n)$. In particular,
is it true that $f(n) \geq n/4$?

In other words, estimate the minimal independence number of a unit distance
graph with $n$ vertices. If $\omega$ is the independence number and $\chi$ is the
chromatic number then $\omega\chi \geq n$, and hence $f(n) \geq n/\chi$, where $\chi$ is
the answer to the Hadwiger–Nelson problem
[erdosproblems.com/508](https://www.erdosproblems.com/508).

The problem is stated in [Er87b, p.171] and is OPEN (page edition 22 January 2026).

The Moser spindle shows $f(n) \leq (2/7)n \approx 0.285n$ (exactly: $f(7m) \leq 2m$ via
disjoint far-apart copies of the spindle; for $7 \nmid n$ spindle unions only give
$f(n) \leq (2/7)n + O(1)$). Larman and Rogers [LaRo72] noted that $f(n) \geq m_1 n$,
where $m_1$ is the supremum of the upper densities of measurable subsets of
$\mathbb{R}^2$ with no two points at distance $1$ (see
[erdosproblems.com/232](https://www.erdosproblems.com/232) for more on $m_1$). Croft
[Cr67] gave the best-known lower bound $m_1 \geq 0.22936$, and hence
$0.22936n \leq f(n) \leq (2/7)n$. Ambrus, Csiszárik, Matolcsi, Varga, and Zsámboki
[ACMVZ23] proved that $m_1 \leq 0.247$, so the density approach alone cannot achieve
$f(n) \geq n/4$. Matolcsi, Ruzsa, Varga, and Zsámboki [MRVZ23] improved the upper bound
to $f(n) \leq (1/4 + o(1))n$; they conjecture that $m_1 = 0.22936\cdots$ (Croft's lower
bound) and that $f(n) = (1/4 + o(1))n$.

If one also insists that no two points are at distance $< 1$ apart, the problem becomes
[erdosproblems.com/1066](https://www.erdosproblems.com/1066).

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_. Intuitive
geometry (Siófok, 1985) (1987), 167–177.

[Cr67] Croft, H. T., _Incidence incidents_, Eureka (1967), 22–26.

[LaRo72] Larman, D. G. and Rogers, C. A., _The realization of distances within sets in
Euclidean space_. Mathematika 19 (1972), 1–24.

[ACMVZ23] Ambrus, G., Csiszárik, A., Matolcsi, M., Varga, D., and Zsámboki, P.,
_The density of planar sets avoiding unit distances_, 2023.

[MRVZ23] Matolcsi, M., Ruzsa, I. Z., Varga, D., and Zsámboki, P.,
_The fractional chromatic number of the plane is at least 4_, 2023.
-/

namespace Erdos1070

/--
**Erdős Problem #1070**, main conjecture [Er87b]:

Is it true that for every $n \geq 1$ and every placement of $n$ distinct points in
$\mathbb{R}^2$, there exists a subset of at least $n/4$ points with no two at distance
exactly $1$ (an independent set in the unit distance graph)?

The injectivity hypothesis makes the $n$ points distinct, matching the source's
"given any $n$ points". Without it the right-hand side would quantify over point
*multisets* — the formally stronger weighted version of the question, which is
potentially a different question at the exact threshold $n/4$.
-/
@[category research open, AMS 5 52]
theorem erdos_1070 : answer(sorry) ↔
    ∀ (n : ℕ), n ≥ 1 → ∀ (f : Fin n → EuclideanSpace ℝ (Fin 2)),
      Function.Injective f →
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ (n : ℝ) / 4 ∧
        ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem #1070**, lower bound [Cr67], [LaRo72]:

For every $n \geq 1$ and every placement of $n$ distinct points in $\mathbb{R}^2$, there
exists a subset of at least $0.22936n$ points with no two at distance exactly $1$.

This follows from Croft's bound $m_1 \geq 0.22936$ [Cr67] combined with the observation
of Larman and Rogers [LaRo72] that $f(n) \geq m_1 n$. (The averaging argument in fact
proves the statement without the injectivity hypothesis as well.)
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.lower_bound (n : ℕ) (hn : n ≥ 1)
    (f : Fin n → EuclideanSpace ℝ (Fin 2)) (hf : Function.Injective f) :
    ∃ S : Finset (Fin n),
      (S.card : ℝ) ≥ 22936 / 100000 * (n : ℝ) ∧  -- 0.22936
      ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1 := by
  sorry

/--
**Erdős Problem #1070**, upper bound (Moser spindle):

For every $m \geq 1$ there is a placement of $7m$ distinct points in $\mathbb{R}^2$
($m$ pairwise far-apart copies of the Moser spindle, which has $7$ vertices and
independence number $2$) such that every independent set in the unit distance graph has
size at most $2m = \frac{2}{7} \cdot 7m$.

This is the exact content of "the Moser spindle shows $f(n) \leq (2/7)n$". For
$7 \nmid n$, disjoint spindle unions only give $f(n) \leq 2\lceil n/7\rceil =
(2/7)n + O(1)$, and the clean bound $f(n) \leq (2/7)n$ for all sufficiently large $n$ is
only known via the stronger asymptotic bound of [MRVZ23] (see
`erdos_1070.variants.upper_bound_asymptotic`).
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.upper_bound (m : ℕ) (hm : m ≥ 1) :
    ∃ f : Fin (7 * m) → EuclideanSpace ℝ (Fin 2),
      Function.Injective f ∧
      ∀ S : Finset (Fin (7 * m)),
        (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
        S.card ≤ 2 * m := by
  sorry

/--
**Erdős Problem #1070**, improved upper bound [MRVZ23]:

Matolcsi, Ruzsa, Varga, and Zsámboki proved $f(n) \leq (1/4 + o(1))n$: for every
$\varepsilon > 0$ and all sufficiently large $n$, there is a placement of $n$ distinct
points in $\mathbb{R}^2$ such that every independent set in the unit distance graph has
size at most $(1/4 + \varepsilon)n$. They conjecture this is sharp, i.e.
$f(n) = (1/4 + o(1))n$.
-/
@[category research solved, AMS 5 52]
theorem erdos_1070.variants.upper_bound_asymptotic (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      ∃ f : Fin n → EuclideanSpace ℝ (Fin 2),
        Function.Injective f ∧
        ∀ S : Finset (Fin n),
          (∀ i ∈ S, ∀ j ∈ S, i ≠ j → dist (f i) (f j) ≠ 1) →
          (S.card : ℝ) ≤ (1 / 4 + ε) * (n : ℝ) := by
  sorry

end Erdos1070
