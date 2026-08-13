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
# Erdős Problem 1069

*Reference:* [erdosproblems.com/1069](https://www.erdosproblems.com/1069)

Given any $n$ points in $\mathbb{R}^2$, the number of $k$-rich lines (lines containing
$\ge k$ of the points) is $\ll n^2 / k^3$, provided $k \le \sqrt{n}$.

Conjectured by Erdős, Croft, and Purdy [Er87b]. Proved by Szemerédi and Trotter [SzTr83],
so the problem is SOLVED.

The best possible value of the implied constant is unknown. When $k = n^{1/2}$ the lattice
points show that there can be $\ge (2 + o(1)) n^{1/2}$ many $n^{1/2}$-rich lines. Erdős
thought that perhaps this is best possible, but Sah [Sa87] gave a construction achieving
$\ge (3 + o(1)) n^{1/2}$ many $n^{1/2}$-rich lines.

[Er87b] Erdős, P., _Some combinatorial and metric problems in geometry_,
Intuitive geometry (Siófok, 1985), 1987, pp. 167–177. (see p. 169)

[Sa87] Sah, C.-H., _The rich line problem of P. Erdős_, 1987, pp. 123–125.

[SzTr83] Szemerédi, E. and Trotter, W.T., _Extremal problems in discrete geometry_,
Combinatorica 3 (1983), 381–392.
-/

namespace Erdos1069

/-- A line in $\mathbb{R}^2$ (represented as `Fin 2 → ℝ`): a set of the form
$\{p + t \cdot d \mid t \in \mathbb{R}\}$ for some point $p$ and nonzero direction $d$. -/
def IsLine (L : Set (Fin 2 → ℝ)) : Prop :=
  ∃ (p d : Fin 2 → ℝ), d ≠ 0 ∧ L = {q : Fin 2 → ℝ | ∃ t : ℝ, q = p + t • d}

open Classical in
/-- The number of $k$-rich lines determined by a finite point set $S \subseteq \mathbb{R}^2$:
lines containing at least $k$ points of $S$.

Note: `Set.ncard` returns the junk value `0` on infinite sets. For $k \ge 2$ the set of
$k$-rich lines is always finite (each such line is determined by two of its points of $S$,
so there are at most $\binom{|S|}{2}$ of them) and the count is genuine; for $k \le 1$
(and $S$ nonempty) there are infinitely many $k$-rich lines and the value is the junk `0`,
which is why the main theorem assumes $2 \le k$. -/
noncomputable def numKRichLines (S : Finset (Fin 2 → ℝ)) (k : ℕ) : ℕ :=
  Set.ncard {L : Set (Fin 2 → ℝ) | IsLine L ∧ k ≤ (S.filter (· ∈ L)).card}

/--
Erdős Problem 1069 (Szemerédi–Trotter theorem) [Er87b], [SzTr83]:

There exists a constant $C > 0$ such that for any finite set $S$ of $n$ points in $\mathbb{R}^2$
and any integer $k$ with $2 \le k$ and $k^2 \le n$, the number of lines containing at
least $k$ points of $S$ is at most $C \cdot n^2 / k^3$.

The hypothesis $k^2 \le n$ encodes the source's condition $k \le n^{1/2}$ exactly (over ℕ
these are equivalent). The hypothesis $2 \le k$ excludes the degenerate cases $k \le 1$,
where every line through a point of $S$ is $k$-rich and the count is infinite (the source's
bound is only meaningful for $k \ge 2$).
-/
@[category research solved, AMS 5 52]
theorem erdos_1069 :
    ∃ C : ℝ, C > 0 ∧
    ∀ (S : Finset (Fin 2 → ℝ)) (k : ℕ),
      2 ≤ k → (k : ℝ) ^ 2 ≤ (S.card : ℝ) →
      (numKRichLines S k : ℝ) ≤ C * (S.card : ℝ) ^ 2 / (k : ℝ) ^ 3 := by
  sorry

/--
When $k = n^{1/2}$, the bound in `erdos_1069` is tight up to the value of the constant:
the $m \times m$ grid of lattice points ($n = m^2$ points) determines
$\ge (2 + o(1)) m$ many $m$-rich lines (its $m$ rows and $m$ columns already give $2m$).

Formalized as: for every $\varepsilon > 0$ and all sufficiently large $m$, there is a set
of $m^2$ points in $\mathbb{R}^2$ with at least $(2 - \varepsilon) m$ many $m$-rich lines.
-/
@[category research solved, AMS 5 52]
theorem erdos_1069.variants.lattice_lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ S : Finset (Fin 2 → ℝ), S.card = m ^ 2 ∧
        (2 - ε) * (m : ℝ) ≤ (numKRichLines S m : ℝ) := by
  sorry

/--
Erdős thought that the lattice lower bound $(2 + o(1)) n^{1/2}$ for the number of
$n^{1/2}$-rich lines determined by $n$ points might be best possible, but Sah [Sa87] gave
a construction achieving $\ge (3 + o(1)) n^{1/2}$ many $n^{1/2}$-rich lines.

Formalized as: for every $\varepsilon > 0$ and all sufficiently large $m$, there is a set
of $m^2$ points in $\mathbb{R}^2$ with at least $(3 - \varepsilon) m$ many $m$-rich lines.
-/
@[category research solved, AMS 5 52]
theorem erdos_1069.variants.sah_lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      ∃ S : Finset (Fin 2 → ℝ), S.card = m ^ 2 ∧
        (3 - ε) * (m : ℝ) ≤ (numKRichLines S m : ℝ) := by
  sorry

end Erdos1069
