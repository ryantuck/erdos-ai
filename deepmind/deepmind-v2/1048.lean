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
# Erdős Problem 1048

Erdős, Herzog, and Piranian asked whether, for a monic polynomial over ℂ with all roots in a
disk of radius r < 2, the sublevel set {z : |f(z)| < 1} must contain a connected component of
diameter greater than 2 − r. Pommerenke disproved this for r > 1; for 0 < r ≤ 1 the answer
is yes.

The problem page (edition 15 September 2025, accessed 2026-02-22) lists the problem as
DISPROVED (LEAN): "This has been solved in the negative and the proof verified in Lean."

Pommerenke [Po61] also proved refined positive results: if 0 ≤ r ≤ 1/2 then the component
containing 0 has diameter ≥ 2, which f(z) = zⁿ shows is best possible; if
1/2 < r ≤ (√5 − 1)/2 then the component containing 0 has diameter > 1/r; and if
(√5 − 1)/2 ≤ r ≤ 1 then the component containing 0 has diameter > 2 − r². (At r = 1 the
last statement requires care for the strict sublevel set: for f(z) = z − 1 the point 0 lies
on the boundary of {z : |f(z)| < 1}, not in it.) The example
f(z) = (zⁿ + 1)(z − 1)²(z − ω)⁻¹(z − ω̄)⁻¹ with ω = e^{iπ/n} shows that the maximum
diameter can be < 1 + o(1) when r = 1.

*Reference:* [erdosproblems.com/1048](https://www.erdosproblems.com/1048)

[EHP58] Erdős, P., Herzog, F. and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., *On metric properties of complex polynomials*,
Michigan Math. J. 8 (1961), 97-115.
-/

open Polynomial Metric

namespace Erdos1048

/--
Erdős Problem 1048 [EHP58, p.142] (disproved by Pommerenke [Po61]):

If $f \in \mathbb{C}[x]$ is a monic polynomial with all roots satisfying $|z| \leq r$ for some
$r < 2$, must $\{ z : |f(z)| < 1 \}$ have a connected component with diameter $> 2 - r$?

Pommerenke [Po61] proved the answer is no for $r > 1$, showing that if
$f(z) = z^n - r^n$ then $\{ z : |f(z)| \leq 1 \}$ has $n$ connected components, all with
diameter $\to 0$ as $n \to \infty$.

For $0 < r \leq 1$, the answer is yes (also Pommerenke [Po61]).

The hypothesis $0 < f.\mathrm{natDegree}$ restricts to nonconstant $f$: the constant monic
polynomial $f = 1$ has no roots (so satisfies the root condition vacuously) and empty
sublevel set, which would otherwise falsify the universal statement at every $r$ for a
degenerate reason — in particular on $0 < r \leq 1$, where the true answer is yes.
-/
@[category research solved, AMS 30]
theorem erdos_1048 : answer(False) ↔
    ∀ (r : ℝ), 0 < r → r < 2 → ∀ (f : Polynomial ℂ), f.Monic → 0 < f.natDegree →
      (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      let S := {z : ℂ | ‖eval z f‖ < 1}
      ∃ z ∈ S, 2 - r < diam (connectedComponentIn S z) := by
  sorry

/--
Pommerenke's disproof [Po61] for radii $1 < r < 2$: there is a monic polynomial with all
roots in the closed disk of radius $r$ whose sublevel set $\{ z : |f(z)| < 1 \}$ has every
connected component of diameter at most $2 - r$. Witnessed by $f(z) = z^n - r^n$ for $n$
large, whose sublevel set $\{ z : |f(z)| \leq 1 \}$ has $n$ connected components with
diameter $\to 0$ as $n \to \infty$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.no_for_r_gt_one :
    ∀ (r : ℝ), 1 < r → r < 2 → ∃ (f : Polynomial ℂ), f.Monic ∧ 0 < f.natDegree ∧
      (∀ z ∈ f.roots, ‖z‖ ≤ r) ∧
      let S := {z : ℂ | ‖eval z f‖ < 1}
      ∀ z ∈ S, diam (connectedComponentIn S z) ≤ 2 - r := by
  sorry

/--
Pommerenke's positive result [Po61] for radii $0 < r \leq 1$: every monic nonconstant
polynomial with all roots in the closed disk of radius $r$ has a connected component of
$\{ z : |f(z)| < 1 \}$ with diameter $> 2 - r$.
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.yes_for_r_le_one :
    ∀ (r : ℝ), 0 < r → r ≤ 1 → ∀ (f : Polynomial ℂ), f.Monic → 0 < f.natDegree →
      (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      let S := {z : ℂ | ‖eval z f‖ < 1}
      ∃ z ∈ S, 2 - r < diam (connectedComponentIn S z) := by
  sorry

/--
Pommerenke's refined bound [Po61] for $0 \leq r \leq 1/2$: the connected component of
$\{ z : |f(z)| < 1 \}$ containing $0$ has diameter $\geq 2$, which $f(z) = z^n$ shows is
best possible. (Note $0$ does lie in the sublevel set here: $|f(0)| \leq r^n \leq 2^{-n} < 1$
since $f$ is monic and nonconstant with all roots of modulus $\leq r$.)
-/
@[category research solved, AMS 30]
theorem erdos_1048.variants.diam_ge_two_of_r_le_half :
    ∀ (r : ℝ), 0 ≤ r → r ≤ 1 / 2 → ∀ (f : Polynomial ℂ), f.Monic → 0 < f.natDegree →
      (∀ z ∈ f.roots, ‖z‖ ≤ r) →
      let S := {z : ℂ | ‖eval z f‖ < 1}
      2 ≤ diam (connectedComponentIn S (0 : ℂ)) := by
  sorry

end Erdos1048
