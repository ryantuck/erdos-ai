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
# Erdős Problem 1039

*Reference:* [erdosproblems.com/1039](https://www.erdosproblems.com/1039)

Let $f(z) = \prod_{i=1}^{n} (z - z_i) \in \mathbb{C}[z]$ with $|z_i| \le 1$ for all $i$. Let
$\rho(f)$ be the radius of the largest disc contained in $\{z : |f(z)| < 1\}$.

Determine the behaviour of $\rho(f)$. In particular, is it always true that $\rho(f) \gg 1/n$?

A problem of Erdős, Herzog, and Piranian [EHP58, p.134]. The problem is open (page edition
27 December 2025).

Known results:
- $f(z) = z^n - 1$ gives $\rho(f) \le \pi/(2n)$
- Pommerenke [Po61] proved $\rho(f) \ge 1/(2en^2)$
- Krishnapur, Lundberg, Ramachandran [KLR25] proved $\rho(f) \gg 1/(n\sqrt{\log n})$

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_. J. Analyse
Math. 6 (1958), 125-148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_. Michigan Math. J. 8 (1961),
97–115.

[KLR25] Krishnapur, M., Lundberg, E., and Ramachandran, K., _On the area of polynomial
lemniscates_. arXiv:2503.18270 (2025).
-/

open Polynomial

namespace Erdos1039

/-- The sublevel radius $\rho(f)$: the supremum of radii $r > 0$ such that some open
disc of radius $r$ is contained in $\{z : \|f(z)\| < 1\}$.

For polynomials outside the scope of the problem the `sSup` falls back to the junk value
`0` (empty radius set, e.g. `f = 1`) or `0` again (unbounded radius set, e.g. `f = 0`,
whose sublevel set is all of $\mathbb{C}$); under the theorem's hypotheses (monic, degree
$n \ge 1$, roots in the closed unit disk) the radius set is nonempty — small discs around
any root qualify — and bounded above by $2$, since $|f(z)| \ge (|z|-1)^n \ge 1$ for
$|z| \ge 2$, so the supremum is a genuine (positive, finite) largest-disc radius. -/
noncomputable def sublevelRadius (f : Polynomial ℂ) : ℝ :=
  sSup {r : ℝ | r > 0 ∧ ∃ c : ℂ, Metric.ball c r ⊆ {z : ℂ | ‖f.eval z‖ < 1}}

/--
Erdős Problem 1039 [EHP58, p.134]:

Is it always true that $\rho(f) \gg 1/n$? That is, is there an absolute constant
$C > 0$ such that every monic complex polynomial of degree $n \ge 1$ with all
roots in the closed unit disk satisfies $\rho(f) \ge C/n$?

This is open. The example $f(z) = z^n - 1$ shows $\rho(f) \le \pi/(2n)$, so the
conjectured rate $1/n$ would be optimal.
-/
@[category research open, AMS 30]
theorem erdos_1039 : answer(sorry) ↔
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : Polynomial ℂ),
      1 ≤ n → f.Monic → f.natDegree = n →
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) →
      sublevelRadius f ≥ C / (n : ℝ) := by
  sorry

/--
Erdős, Herzog, and Piranian [EHP58, p.134] note that $f(z) = z^n - 1$ has
$\rho(f) \le \frac{\pi/2}{n}$, so the rate $1/n$ in Erdős Problem 1039 cannot
be improved.
-/
@[category research solved, AMS 30]
theorem erdos_1039.variants.roots_of_unity_upper (n : ℕ) (hn : 1 ≤ n) :
    sublevelRadius ((X : Polynomial ℂ) ^ n - 1) ≤ Real.pi / (2 * (n : ℝ)) := by
  sorry

/--
Pommerenke [Po61] proved that every monic complex polynomial of degree $n \ge 1$
with all roots in the closed unit disk satisfies
$\rho(f) \ge \frac{1}{2en^2}$.
-/
@[category research solved, AMS 30]
theorem erdos_1039.variants.pommerenke_lower (n : ℕ) (f : Polynomial ℂ)
    (hn : 1 ≤ n) (hf : f.Monic) (hdeg : f.natDegree = n)
    (hroots : ∀ z ∈ f.roots, ‖z‖ ≤ 1) :
    sublevelRadius f ≥ 1 / (2 * Real.exp 1 * (n : ℝ) ^ 2) := by
  sorry

/--
Krishnapur, Lundberg, and Ramachandran [KLR25] proved
$\rho(f) \gg \frac{1}{n\sqrt{\log n}}$ for monic polynomials with all roots in
the closed unit disk.

The bound is stated for all $n \ge 2$ with a uniform constant; this is
equivalent to the asymptotic form, since for each of the finitely many small
$n$ Pommerenke's bound $\rho(f) \ge 1/(2en^2) > 0$ holds uniformly in $f$, so
the constant can be shrunk to cover them. ($n = 2$ is the natural starting
point: at $n = 1$ the right-hand side degenerates because $\log 1 = 0$ and
Lean's division-by-zero convention would render the inequality trivial.)
-/
@[category research solved, AMS 30]
theorem erdos_1039.variants.klr_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : Polynomial ℂ),
      2 ≤ n → f.Monic → f.natDegree = n →
      (∀ z ∈ f.roots, ‖z‖ ≤ 1) →
      sublevelRadius f ≥ C / ((n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by
  sorry

end Erdos1039
