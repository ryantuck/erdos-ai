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
# Erdős Problem 1045

*Reference:* [erdosproblems.com/1045](https://www.erdosproblems.com/1045)

Let $z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i - z_j| \le 2$ for all $i, j$, and
$$\Delta(z_1, \ldots, z_n) = \prod_{i \neq j} |z_i - z_j|.$$

What is the maximum possible value of $\Delta$? Is it maximised by taking the $z_i$
to be the vertices of a regular polygon?

A problem of Erdős, Herzog, and Piranian [EHP58, p.143], who proved that, for any
monic polynomial $f$, if $\{z : |f(z)| < 1\}$ is connected and $f$ has roots
$z_1, \ldots, z_n$, then $\prod_{i \neq j} |z_i - z_j| < n^n$.

The value of $\Delta$ when the $z_i$ are the vertices of a regular polygon (scaled so
that the point set has diameter $2$, the extremal admissible scaling) is $n^n$ when $n$
is even and $\cos(\pi/2n)^{-n(n-1)} n^n \sim e^{\pi^2/8} n^n$ when $n$ is odd. Note
that only for even $n$ is this polygon inscribed in a circle of diameter $2$: for odd
$n$ the longest diagonal is shorter than the circumdiameter, so the extremal regular
polygon has circumradius $1/\cos(\pi/2n) > 1$.

Pommerenke [Po61] proved the upper bound $\Delta \le 2^{O(n)} n^n$. Hu and Tang found
counterexamples for $n = 4$ and $n = 6$, and Cambie showed that the regular polygon
does not maximise $\Delta$ for any even $n \ge 4$, so the answer to the second question
is "no" in general. It is now known that, for even $n$,
$$\liminf \frac{\max \Delta}{n^n} \ge C$$
for some $C > 0$: Sothanaphan [So25] proved this with $C \approx 1.0378$, and
constructions of Cambie, Dong, and Tang achieve $C \approx 1.304457$ when $6 \mid n$
and $C \approx 1.26853$ for all even $n$.

It remains possible that the regular polygon is a maximiser for odd $n$, and the value
question ("what is the maximum possible value of $\Delta$?") is not settled; the source
page records the problem as OPEN (falsifiable). [Page last edited 30 December 2025,
accessed 2026-02-22. Tags: analysis.]

[EHP58] Erdős, P., Herzog, F., and Piranian, G., _Metric properties of polynomials_,
J. Analyse Math. **6** (1958), 125–148.

[Po61] Pommerenke, Ch., _On metric properties of complex polynomials_,
Michigan Math. J. **8** (1961), 97–115.

[So25] Sothanaphan, N., _An improved lower bound to Erdős' problem concerning
products of distances for fixed diameter_, arXiv:2512.14251 (2025).
-/

open Complex Finset BigOperators

namespace Erdos1045

/-- The product $\Delta(z) = \prod_{i \neq j} \|z_i - z_j\|$ (over ordered pairs
$i \neq j$) for a configuration $z : \mathrm{Fin}\; n \to \mathbb{C}$. -/
noncomputable def erdosDelta (n : ℕ) (z : Fin n → ℂ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i ≠ j then ‖z i - z j‖ else 1

/-- The vertices of a regular $n$-gon inscribed in the unit circle (circumradius $1$),
namely $e^{2\pi i k/n}$ for $k = 0, \ldots, n-1$. For even $n$ this is the regular
$n$-gon of diameter $2$; for odd $n$ the diameter-$2$ regular $n$-gon is this one
scaled by $1/\cos(\pi/2n) > 1$. -/
noncomputable def regularNGon (n : ℕ) : Fin n → ℂ :=
  fun k => exp (ofReal (2 * Real.pi * (k.val : ℝ) / (n : ℝ)) * I)

/-- `w : Fin n → ℂ` lists the vertices of a regular $n$-gon: for some centre $c$ and
some $\rho \in \mathbb{C} \setminus \{0\}$ (encoding scale and rotation),
$w_k = c + \rho e^{2\pi i k/n}$. (Degenerate for $n \le 2$ — any point, resp. any pair
of distinct points — which is harmless in the statements below.) -/
def IsRegularNGon (n : ℕ) (w : Fin n → ℂ) : Prop :=
  ∃ c ρ : ℂ, ρ ≠ 0 ∧
    ∀ k, w k = c + ρ * exp (ofReal (2 * Real.pi * (k.val : ℝ) / (n : ℝ)) * I)

/--
Erdős Problem 1045 [EHP58, p.143]:

Is it true that for all $n \ge 1$, the maximum of
$\Delta(z_1, \ldots, z_n) = \prod_{i \neq j} |z_i - z_j|$ over all
$z_1, \ldots, z_n \in \mathbb{C}$ with $|z_i - z_j| \le 2$ is attained when the $z_i$
are the vertices of a regular $n$-gon?

The answer is no: Hu and Tang found counterexamples for $n = 4$ and $n = 6$, and
Cambie showed that no regular polygon is a maximiser for any even $n \ge 4$.
-/
@[category research solved, AMS 30]
theorem erdos_1045 : answer(False) ↔
    ∀ (n : ℕ) (_ : n ≥ 1), ∃ w : Fin n → ℂ, IsRegularNGon n w ∧
      (∀ i j : Fin n, ‖w i - w j‖ ≤ 2) ∧
      ∀ (z : Fin n → ℂ) (_ : ∀ i j : Fin n, ‖z i - z j‖ ≤ 2),
        erdosDelta n z ≤ erdosDelta n w := by
  sorry

/--
The conjecture remains open for odd $n$: for every odd $n \ge 1$, is the maximum of
$\Delta$ over all admissible configurations attained by the vertices of a regular
$n$-gon? (The extremal regular $n$-gon for odd $n$ has diameter $2$ and circumradius
$1/\cos(\pi/2n)$, with $\Delta = \cos(\pi/2n)^{-n(n-1)} n^n$.)
-/
@[category research open, AMS 30]
theorem erdos_1045.variants.odd : answer(sorry) ↔
    ∀ (n : ℕ) (_ : n ≥ 1) (_ : Odd n), ∃ w : Fin n → ℂ, IsRegularNGon n w ∧
      (∀ i j : Fin n, ‖w i - w j‖ ≤ 2) ∧
      ∀ (z : Fin n → ℂ) (_ : ∀ i j : Fin n, ‖z i - z j‖ ≤ 2),
        erdosDelta n z ≤ erdosDelta n w := by
  sorry

/--
For even $n$, the value of $\Delta$ at the vertices of the regular $n$-gon of
diameter $2$ (which is inscribed in the unit circle) is $n^n$.
-/
@[category research solved, AMS 30]
theorem erdos_1045.variants.even_value (n : ℕ) (hn : 1 ≤ n) (he : Even n) :
    erdosDelta n (regularNGon n) = (n : ℝ) ^ n := by
  sorry

/--
Hu–Tang ($n = 4, 6$) and Cambie (all even $n \ge 4$): for every even $n \ge 4$ there
is an admissible configuration with $\Delta$ strictly larger than that of every
admissible regular $n$-gon, i.e. no regular polygon is a maximiser.
-/
@[category research solved, AMS 30]
theorem erdos_1045.variants.even_not_maximiser (n : ℕ) (hn : 4 ≤ n) (he : Even n) :
    ∃ z : Fin n → ℂ, (∀ i j : Fin n, ‖z i - z j‖ ≤ 2) ∧
      ∀ w : Fin n → ℂ, IsRegularNGon n w → (∀ i j : Fin n, ‖w i - w j‖ ≤ 2) →
        erdosDelta n w < erdosDelta n z := by
  sorry

/--
Pommerenke [Po61] proved that $\Delta \le 2^{O(n)} n^n$ for all $z_i$ with
$|z_i - z_j| \le 2$, encoded here as: there is a constant $C > 0$ such that
$\Delta(z) \le C^n n^n$ for all $n$ and all admissible configurations $z$.
-/
@[category research solved, AMS 30]
theorem erdos_1045.variants.pommerenke_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : Fin n → ℂ),
      (∀ i j : Fin n, ‖z i - z j‖ ≤ 2) → erdosDelta n z ≤ C ^ n * (n : ℝ) ^ n := by
  sorry

/--
For even $n$ the maximum of $\Delta$ asymptotically exceeds the regular-polygon value
$n^n$ by a constant factor: there are $C > 1$ and $N$ such that every even $n \ge N$
admits an admissible configuration with $\Delta \ge C n^n$. This is a consequence of
$\liminf (\max \Delta)/n^n \ge C$ over even $n$, proved with $C \approx 1.0378$ by
Sothanaphan [So25]; constructions of Cambie, Dong, and Tang achieve
$C \approx 1.304457$ when $6 \mid n$ and $C \approx 1.26853$ for all even $n$.
-/
@[category research solved, AMS 30]
theorem erdos_1045.variants.even_asymptotic_lower :
    ∃ C : ℝ, 1 < C ∧ ∃ N : ℕ, ∀ (n : ℕ), N ≤ n → Even n →
      ∃ z : Fin n → ℂ, (∀ i j : Fin n, ‖z i - z j‖ ≤ 2) ∧
        C * (n : ℝ) ^ n ≤ erdosDelta n z := by
  sorry

end Erdos1045
