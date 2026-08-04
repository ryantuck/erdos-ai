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
# Erdős Problem 1083

*Reference:* [erdosproblems.com/1083](https://www.erdosproblems.com/1083)

Let $d \geq 3$, and let $f_d(n)$ be the minimal $m$ such that every set of $n$ points
in $\mathbb{R}^d$ determines at least $m$ distinct distances. Estimate $f_d(n)$ — in
particular, is it true that $f_d(n) = n^{2/d - o(1)}$?

This is a generalisation of the distinct distances problem
[erdosproblems.com/89](https://www.erdosproblems.com/89) to higher dimensions.
Erdős [Er46b] proved $n^{1/d} \ll_d f_d(n) \ll_d n^{2/d}$, the upper bound
construction being given by a set of lattice points. Partial results towards
the conjectured lower bound:

- Clarkson, Edelsbrunner, Guibas, Sharir, and Welzl [CEGSW90] proved
  $f_3(n) \gg n^{1/2}$.
- Aronov, Pach, Sharir, and Tardos [APST04] proved
  $f_d(n) \gg n^{\frac{1}{d - 90/77} - o(1)}$ for any $d \geq 3$
  (for example, $f_3(n) \gg n^{0.546}$).
- Solymosi and Vu [SoVu08] proved $f_3(n) \gg n^{3/5}$ and
  $f_d(n) \gg_d n^{\frac{2}{d} - \frac{c}{d^2}}$ for all $d \geq 4$ for some
  constant $c > 0$. (The $d = 3$ bound as recorded on the problem page combines
  their method with the work of Guth and Katz on the planar problem.)

The function $f_d(n)$ is essentially the inverse of the function $g_d(n)$ of
[erdosproblems.com/1089](https://www.erdosproblems.com/1089): with these
definitions, $g_d(n) > m$ if and only if $f_d(m) < n$. The emphasis in this
problem is on the behaviour as $d$ is fixed and $n \to \infty$.

The problem is OPEN (page last edited 16 October 2025, accessed 2026-02-22).

[Er46b] Erdős, P., _On sets of distances of $n$ points_. Amer. Math. Monthly (1946), 248-250.

[Er75f] Erdős, P., _On some problems of elementary and combinatorial geometry_.
Ann. Mat. Pura Appl. (4) (1975), 99-108.

[CEGSW90] Clarkson, K. L., Edelsbrunner, H., Guibas, L. J., Sharir, M., Welzl, E.,
_Combinatorial complexity bounds for arrangements of curves and spheres_.
Discrete Comput. Geom. (1990), 99-160.

[APST04] Aronov, B., Pach, J., Sharir, M., Tardos, G.,
_Distinct distances in three and higher dimensions_.
Combin. Probab. Comput. (2004), 283-293.

[SoVu08] Solymosi, J., Vu, V. H., _Near optimal bounds for the Erdős distinct
distances problem in high dimensions_. Combinatorica (2008), 113-125.
-/

namespace Erdos1083

/-- The number of distinct pairwise distances determined by a finite point set
in $\mathbb{R}^d$. -/
noncomputable def distinctDistanceCount {d : ℕ} (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  Set.ncard {r : ℝ | ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ r = dist p q}

/-- $f_d(n)$: the minimal number of distinct distances determined by any set of
$n$ points in $\mathbb{R}^d$. -/
noncomputable def minDistinctDistances (d : ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (P : Finset (EuclideanSpace ℝ (Fin d))),
    P.card = n ∧ distinctDistanceCount P = m}

/--
**Erdős Problem 1083** [Er46b][Er75f, p.101]:

Is it true that for every $d \geq 3$, $f_d(n) = n^{2/d - o(1)}$? That is, for
all $d \geq 3$ and $\varepsilon > 0$, does
$n^{2/d - \varepsilon} \leq f_d(n) \leq n^{2/d + \varepsilon}$
hold for all sufficiently large $n$?

The upper-bound half is known: Erdős [Er46b] proved $f_d(n) \ll_d n^{2/d}$ via
lattice points, so the open content of the question is the lower bound (see
`erdos_1083.variants.lower_bound`).
-/
@[category research open, AMS 52]
theorem erdos_1083 : answer(sorry) ↔
    ∀ d : ℕ, d ≥ 3 → ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (n : ℝ) ^ ((2 : ℝ) / d - ε) ≤ (minDistinctDistances d n : ℝ) ∧
        (minDistinctDistances d n : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / d + ε) := by
  sorry

/--
The conjectured lower bound: for all $d \geq 3$ and $\varepsilon > 0$, there
exists $N_0$ such that for all $n \geq N_0$, $f_d(n) \geq n^{2/d - \varepsilon}$.

This is the open half of $f_d(n) = n^{2/d - o(1)}$; the matching upper bound
$f_d(n) \ll_d n^{2/d}$ was proved by Erdős [Er46b] via lattice points.
-/
@[category research open, AMS 52]
theorem erdos_1083.variants.lower_bound (d : ℕ) (hd : d ≥ 3) (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (minDistinctDistances d n : ℝ) ≥ (n : ℝ) ^ ((2 : ℝ) / d - ε) := by
  sorry

/--
Erdős [Er46b] proved $n^{1/d} \ll_d f_d(n) \ll_d n^{2/d}$, the upper bound
construction being given by a set of lattice points.
-/
@[category research solved, AMS 52]
theorem erdos_1083.variants.erdos_bounds (d : ℕ) (hd : d ≥ 3) :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c * (n : ℝ) ^ ((1 : ℝ) / d) ≤ (minDistinctDistances d n : ℝ) ∧
        (minDistinctDistances d n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) / d) := by
  sorry

/--
Clarkson, Edelsbrunner, Guibas, Sharir, and Welzl [CEGSW90] proved
$f_3(n) \gg n^{1/2}$.
-/
@[category research solved, AMS 52]
theorem erdos_1083.variants.cegsw_three_dim :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c * (n : ℝ) ^ ((1 : ℝ) / 2) ≤ (minDistinctDistances 3 n : ℝ) := by
  sorry

/--
Aronov, Pach, Sharir, and Tardos [APST04] proved
$f_d(n) \gg n^{\frac{1}{d - 90/77} - o(1)}$ for any $d \geq 3$
(for example, $f_3(n) \gg n^{0.546}$).
-/
@[category research solved, AMS 52]
theorem erdos_1083.variants.apst (d : ℕ) (hd : d ≥ 3) (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (n : ℝ) ^ ((1 : ℝ) / ((d : ℝ) - 90 / 77) - ε) ≤ (minDistinctDistances d n : ℝ) := by
  sorry

/--
Solymosi and Vu [SoVu08] proved $f_3(n) \gg n^{3/5}$. (As recorded on the
problem page, this combines their method with the Guth–Katz bound for distinct
distances in the plane; the bound in their paper for $d = 3$ alone is slightly
weaker.)
-/
@[category research solved, AMS 52]
theorem erdos_1083.variants.solymosi_vu_three_dim :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c * (n : ℝ) ^ ((3 : ℝ) / 5) ≤ (minDistinctDistances 3 n : ℝ) := by
  sorry

/--
Solymosi and Vu [SoVu08] proved that there is a constant $c > 0$ such that
$f_d(n) \gg_d n^{\frac{2}{d} - \frac{c}{d^2}}$ for all $d \geq 4$.
-/
@[category research solved, AMS 52]
theorem erdos_1083.variants.solymosi_vu_high_dim :
    ∃ c : ℝ, c > 0 ∧ ∀ d : ℕ, d ≥ 4 → ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (n : ℝ) ^ ((2 : ℝ) / d - c / (d : ℝ) ^ 2) ≤ (minDistinctDistances d n : ℝ) := by
  sorry

end Erdos1083
