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
# Erdős Problem 1047

*Reference:* [erdosproblems.com/1047](https://www.erdosproblems.com/1047)

Let $f \in \mathbb{C}[x]$ be a monic polynomial with $m$ distinct roots, and let $c > 0$ be a
constant small enough such that $\{ z : |f(z)| \leq c \}$ has $m$ distinct connected
components. Must all these components be convex?

A question of Grunsky, reported by Erdős, Herzog, and Piranian [EHP58, p.145].

The answer is no, as shown by Pommerenke [Po61], who proved that for
$f(z) = z^k(z-a)$ with $k$ sufficiently large and $a$ close to $(1+1/k)k^{1/(k+1)}$,
the set $\{ z : |f(z)| \leq 1 \}$ has two components and the one containing $0$ is
not convex.

Goodman [Go66] proved that one of the three components of
$\{ z : |(z^2+1)(z-2)^2| < 5^{3/2}/4 \}$ is not convex, and constructed an example with
simple roots, of degree $4$. The referee of that paper also gave the example
$\{ z : |z(z^5-1)| < 5.6^{-6/5} \}$ (constant as rendered on the problem page; the
critical value of $|z(z^5-1)|$ is exactly $5 \cdot 6^{-6/5}$, which suggests that reading).

Goodman raises the question of the maximum number of non-convex components that are
possible as a function of the degree of $f$.

The problem page marks this DISPROVED (LEAN): solved in the negative and the proof
verified in Lean (page last edited 28 October 2025, accessed 2026-02-22).

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_. J. Analyse
Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J. 8 (1961),
97–115.

[Go66] Goodman, A. W., _On the convexity of the level curves of a polynomial_. Proc. Amer. Math.
Soc. 17 (1966), 358-361.
-/

open Complex Polynomial Set

namespace Erdos1047

/--
Erdős Problem 1047 (Grunsky's question, [EHP58, p.145]):

For a monic polynomial $f \in \mathbb{C}[x]$ with $m$ distinct roots and $c > 0$ such that
the sublevel set $S = \{ z : \|f(z)\| \leq c \}$ has exactly $m$ connected components,
must all these components be convex?

Answered in the negative by Pommerenke [Po61].
-/
@[category research solved, AMS 30 52]
theorem erdos_1047 : answer(False) ↔
    ∀ (f : Polynomial ℂ), f.Monic →
    ∀ (c : ℝ), c > 0 →
      let S := {z : ℂ | ‖eval z f‖ ≤ c}
      ncard (connectedComponentIn S '' S) = f.roots.toFinset.card →
      ∀ x ∈ S, Convex ℝ (connectedComponentIn S x) := by
  sorry

/--
Goodman's explicit counterexample [Go66]: one of the three connected components of
$\{ z : |(z^2+1)(z-2)^2| < 5^{3/2}/4 \}$ is not convex. Here $(z^2+1)(z-2)^2$ is monic
with the three distinct roots $i$, $-i$, $2$, and $5^{3/2}/4 = 5\sqrt{5}/4$.

Note the sublevel set here is defined by a *strict* inequality, following the problem
page's quotation of [Go66].
-/
@[category research solved, AMS 30 52]
theorem erdos_1047.variants.goodman :
    let f : Polynomial ℂ := (X ^ 2 + 1) * (X - 2) ^ 2
    let S := {z : ℂ | ‖eval z f‖ < 5 * Real.sqrt 5 / 4}
    ncard (connectedComponentIn S '' S) = 3 ∧
      ∃ x ∈ S, ¬Convex ℝ (connectedComponentIn S x) := by
  sorry

end Erdos1047
