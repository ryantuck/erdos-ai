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
# Erdős Problem 1044

*Reference:* [erdosproblems.com/1044](https://www.erdosproblems.com/1044)

Let $f(z) = \prod_{i=1}^{n} (z - z_i)$ be a monic polynomial with all roots in the closed unit
disk. If $\Lambda(f)$ is the maximum of the lengths of the boundaries of the connected components
of $\{z : |f(z)| < 1\}$, determine the infimum of $\Lambda(f)$ over all such $f$.

A problem of Erdős, Herzog, and Piranian [EHP58]. The problem is **SOLVED**: it was resolved
by Tang [Ta], who proved that the infimum of $\Lambda(f)$ over all such $f$ (of degree
$n \geq 1$) is $2$. Tang also suggests that, if the degree $n$ is fixed, then the infimum over
all such $f$ of degree $n$ is attained by $f_n(z) = z^n - 1$, and proves this for $n = 1$ and
$n = 2$ (page last edited 16 January 2026, accessed 2026-02-22).

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125–148.

[Ta] Tang, Q., *On Erdős Problem 1044*,
[github.com/QuanyuTang/erdos-problem-1044](https://github.com/QuanyuTang/erdos-problem-1044)
(unpublished note linked from the problem page).
-/

open Complex Polynomial MeasureTheory

namespace Erdos1044

/--
The sublevel set $\{z \in \mathbb{C} \mid \|f(z)\| < 1\}$ for a function $f : \mathbb{C} \to \mathbb{C}$.
-/
noncomputable def lemniscateSublevel (f : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | ‖f z‖ < 1}

/--
$\Lambda(f)$: the supremum of the 1-dimensional Hausdorff measures of the frontiers
of the connected components of $\{z \in \mathbb{C} \mid \|f(z)\| < 1\}$. A connected component
containing $x$ in the sublevel set $S$ is `connectedComponentIn S x`.

Note: this computes a supremum (`sSup`), not a literal maximum. For polynomial lemniscates
the number of connected components is finite, so the supremum is attained.

Junk-value warning: if the sublevel set is empty — as happens for the constant function
$f = 1$, i.e. the unique monic polynomial of degree $0$ — the set below is empty and
`sSup ∅ = 0` in `ℝ`, so this definition returns $0$ even though the informal maximum is
undefined. The theorems below therefore restrict to polynomials of positive degree.
Similarly, `ENNReal.toReal` sends an infinite Hausdorff measure to $0$; this is harmless
for polynomial lemniscates, whose component boundaries are algebraic curves of finite length.
-/
noncomputable def maxBoundaryLength (f : ℂ → ℂ) : ℝ :=
  sSup {ℓ : ℝ | ∃ x ∈ lemniscateSublevel f,
    ℓ = (Measure.hausdorffMeasure 1
      (frontier (connectedComponentIn (lemniscateSublevel f) x))).toReal}

/--
Erdős Problem 1044 (Erdős–Herzog–Piranian [EHP58]):

Let $f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[z]$, $n \geq 1$, where $|z_i| \leq 1$ for
all $i$. If $\Lambda(f)$ is the maximum of the lengths of the boundaries of the connected
components of $\{z : |f(z)| < 1\}$, then the infimum of $\Lambda(f)$ over all such $f$
equals $2$.

Resolved by Tang [Ta], who proved that the infimum of $\Lambda(f)$ over all such $f$ is $2$.

The hypothesis $0 < \deg f$ is essential: the degree-$0$ monic polynomial $f = 1$ has no
roots (so the root condition holds vacuously) and an empty sublevel set, for which
`maxBoundaryLength` returns the junk value $0$; without excluding it the infimum would be $0$.
-/
@[category research solved, AMS 30]
theorem erdos_1044 :
    sInf {L : ℝ | ∃ (f : Polynomial ℂ), f.Monic ∧ 0 < f.natDegree ∧
      (∀ z, f.IsRoot z → ‖z‖ ≤ 1) ∧
      L = maxBoundaryLength (fun z => f.eval z)} = answer((2 : ℝ)) := by
  sorry

/--
Tang's conjecture [Ta]: For fixed degree $n \geq 1$, the infimum of $\Lambda(f)$ over all monic
polynomials of degree $n$ with roots in the closed unit disk is attained by $f_n(z) = z^n - 1$.
Tang has verified this for $n = 1$ and $n = 2$; the general case is open.
-/
@[category research open, AMS 30]
theorem erdos_1044.variants.fixed_degree (n : ℕ) (hn : 1 ≤ n) :
    maxBoundaryLength (fun z => (X ^ n - 1 : Polynomial ℂ).eval z) =
    sInf {L : ℝ | ∃ (f : Polynomial ℂ), f.Monic ∧ f.natDegree = n ∧
      (∀ z, f.IsRoot z → ‖z‖ ≤ 1) ∧
      L = maxBoundaryLength (fun z => f.eval z)} := by
  sorry

/--
Tang's fixed-degree conjecture holds in degrees $1$ and $2$ [Ta]: for $n \in \{1, 2\}$, the
infimum of $\Lambda(f)$ over all monic polynomials of degree $n$ with roots in the closed unit
disk is attained by $f_n(z) = z^n - 1$.
-/
@[category research solved, AMS 30]
theorem erdos_1044.variants.fixed_degree_one_two (n : ℕ) (hn : n = 1 ∨ n = 2) :
    maxBoundaryLength (fun z => (X ^ n - 1 : Polynomial ℂ).eval z) =
    sInf {L : ℝ | ∃ (f : Polynomial ℂ), f.Monic ∧ f.natDegree = n ∧
      (∀ z, f.IsRoot z → ‖z‖ ≤ 1) ∧
      L = maxBoundaryLength (fun z => f.eval z)} := by
  sorry

end Erdos1044
