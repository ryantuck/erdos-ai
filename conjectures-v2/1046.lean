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
# Erdős Problem 1046

*Reference:* [erdosproblems.com/1046](https://www.erdosproblems.com/1046)

Let $f \in \mathbb{C}[x]$ be a monic polynomial and
$$E = \{ z : \lvert f(z)\rvert < 1 \}.$$
If $E$ is connected then is $E$ contained in a disc of radius $2$?

A problem of Erdős, Herzog, and Piranian [EHP58], who also ask, if
$\{ z : \lvert f(z)\rvert \leq 1 \}$ is connected, then what are the least possible
diameter and greatest possible width of this set, and conjecture the answer is $2$ in
both cases. Their guess that the width is always at most $2$ is false, as Pommerenke
[Po59] gave an example with width $> \sqrt{3} \cdot 2^{1/3} \approx 2.18$. (Compare
problem #1043 on projections of $\{ z : \lvert f(z)\rvert \leq 1 \}$ onto lines.)

The condition that $E$ is connected is equivalent to $E$ containing all zeros of $f'$.

The answer is yes: Pommerenke [Po59] proved that $E$ is contained in the closed disc of
radius $2$ centred at $\frac{z_1 + \cdots + z_n}{n}$, where the $z_i$ are the roots
of $f$.

Note on status: the problem page's banner marks #1046 DISPROVED ("This has been solved
in the negative"), which refers to the Erdős–Herzog–Piranian width conjecture recorded
in the remarks; the literal radius-$2$ question displayed on the page was answered
affirmatively by Pommerenke (page last edited 15 September 2025, accessed 2026-02-22;
tag: analysis).

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125-148.

[Po59] Pommerenke, Ch., *On some problems by Erdős, Herzog and Piranian*,
Michigan Math. J. 6 (1959), 221-225.
-/

open Complex Polynomial Metric Set

namespace Erdos1046

/--
Erdős Problem 1046 [EHP58, p. 143]:

Let $f \in \mathbb{C}[x]$ be a monic polynomial and
$E = \{ z \in \mathbb{C} : |f(z)| < 1 \}$. If $E$ is connected, then is $E$ contained
in a (closed) disc of radius $2$?

The answer is yes, proved by Pommerenke [Po59].
-/
@[category research solved, AMS 30]
theorem erdos_1046 : answer(True) ↔
    ∀ (f : Polynomial ℂ), f.Monic →
      let E := {z : ℂ | ‖eval z f‖ < 1}
      IsConnected E →
      ∃ c : ℂ, E ⊆ closedBall c 2 := by
  sorry

/--
Strengthening of Erdős Problem 1046: Pommerenke [Po59] proved that the center of the
containing disc of radius $2$ can be taken to be the centroid (arithmetic mean) of the
roots of $f$, i.e., $\frac{z_1 + \cdots + z_n}{n}$.
-/
@[category research solved, AMS 30]
theorem erdos_1046.variants.centroid :
    ∀ (f : Polynomial ℂ), f.Monic →
      let E := {z : ℂ | ‖eval z f‖ < 1}
      IsConnected E →
      E ⊆ closedBall (f.roots.sum / (f.natDegree : ℂ)) 2 := by
  sorry

/--
Width conjecture from [EHP58]: Erdős, Herzog, and Piranian conjectured that if
$\{ z : |f(z)| \leq 1 \}$ is connected, then its width is at most $2$. This was disproved
by Pommerenke [Po59], who gave an example with width $> \sqrt{3} \cdot 2^{1/3} \approx 2.18$.

The width of a planar set $S$ is the infimum over unit directions $u$ of
$\sup_{z_1, z_2 \in S} |\operatorname{Re}((z_1 - z_2) \cdot \bar{u})|$; for nonconstant
monic $f$ the set $\{ z : |f(z)| \leq 1 \}$ is compact, so this infimum is attained and
"width at most $2$" is equivalent to the existential form below.

The hypothesis $0 < \deg f$ is necessary: for the constant polynomial $f = 1$ the set
$\{ z : |f(z)| \leq 1 \}$ is all of $\mathbb{C}$, which is connected but has infinite
width, so without this hypothesis the universally quantified statement would be false
for a trivial reason unrelated to Pommerenke's counterexample.
-/
@[category research solved, AMS 30]
theorem erdos_1046.variants.width : answer(False) ↔
    ∀ (f : Polynomial ℂ), f.Monic → 0 < f.natDegree →
      let E := {z : ℂ | ‖eval z f‖ ≤ 1}
      IsConnected E →
      ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ z₁ ∈ E, ∀ z₂ ∈ E,
        |((z₁ - z₂) * starRingEnd ℂ u).re| ≤ 2 := by
  sorry

end Erdos1046
