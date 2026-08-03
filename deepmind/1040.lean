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
# Erdős Problem 1040

*Reference:* [erdosproblems.com/1040](https://www.erdosproblems.com/1040)

Let $F \subseteq \mathbb{C}$ be a closed infinite set, and let $\mu(F)$ be the infimum of
$|\{z : |f(z)| < 1\}|$ (Lebesgue measure), as $f$ ranges over all polynomials of
the shape $\prod(z - z_i)$ with $z_i \in F$.

Is $\mu(F)$ determined by the transfinite diameter of $F$? In particular, is
$\mu(F) = 0$ whenever the transfinite diameter of $F$ is $\geq 1$?

The transfinite diameter (logarithmic capacity) of $F$ is defined by
$$\rho(F) = \lim_{n \to \infty} \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{1/\binom{n}{2}}.$$

A problem of Erdős, Herzog, and Piranian [EHP58, p.135]. The "in particular" question is
open (page edition 01 February 2026, accessed 2026-02-22). Known results:

- Erdős, Herzog, and Piranian [EHP58] showed the answer to the "in particular" question is
  yes when $F$ is a line segment or disc, and that if the transfinite diameter is $< 1$
  then $\{z : |f(z)| < 1\}$ always contains a disc of radius $\gg_F 1$.
- Erdős and Netanyahu [ErNe73] proved that if $F$ is also bounded and connected, with
  transfinite diameter $0 < c < 1$, then $\{z : |f(z)| < 1\}$ always contains a disc of
  radius $\gg_c 1$.
- Aletheia [Fe26] showed that $\mu(F)$ is *not* determined by the transfinite diameter of
  $F$, by producing two distinct closed infinite sets $F_1$ and $F_2$, both of transfinite
  diameter $0$, with $\mu(F_1) \geq \pi/4$ while $\mu(F_2)$ can be made arbitrarily close
  to $0$. This answers the first question negatively; the "in particular" question
  remains open.

[EHP58] Erdős, P., Herzog, F., and Piranian, G., *Metric properties of polynomials*,
J. Analyse Math. **6** (1958), 125–148.

[ErNe73] Erdős, P. and Netanyahu, E., *A remark on polynomials and the transfinite diameter*,
Israel J. Math. (1973), 23–25.

[Fe26] Feng, T. et al., _Semi-Autonomous Mathematics Discovery with Gemini: A Case Study on
the Erdős Problems_. arXiv:2601.22401 (2026).
-/

open scoped ENNReal

open MeasureTheory Classical Filter Finset

namespace Erdos1040

/-- The product of pairwise distances $\prod_{i<j} \|z_i - z_j\|$ for a tuple of
complex numbers. -/
noncomputable def pairwiseDistProd {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ((univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).prod
    (fun p => ‖z p.1 - z p.2‖)

/-- The $n$-th transfinite diameter of $F \subseteq \mathbb{C}$:
$d_n(F) = \sup_{z_1,\ldots,z_n \in F} \left(\prod_{i<j} |z_i - z_j|\right)^{2/(n(n-1))}$. -/
noncomputable def nthTransfiniteDiam (F : Set ℂ) (n : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    t = (pairwiseDistProd z) ^ ((2 : ℝ) / (↑n * (↑n - 1)))}

/-- The transfinite diameter (logarithmic capacity) of $F \subseteq \mathbb{C}$:
$\rho(F) = \lim_{n \to \infty} d_n(F)$.

Degenerate behaviour, for the record: for $n \in \{0, 1\}$ the exponent
$2/(n(n-1))$ is a division by zero, hence $0$, so `nthTransfiniteDiam F 0 =
nthTransfiniteDiam F 1 = 1` (junk, invisible to the limit). For *unbounded* $F$
the achieved-value set in `nthTransfiniteDiam` is unbounded above for every
$n \geq 2$, so `Real.sSup` returns its junk value $0$; the sequence is then
$(1, 1, 0, 0, \ldots)$ and this definition assigns transfinite diameter $0$
(rather than the informal $\infty$) to unbounded sets. In `erdos_1040` this is
harmless: unbounded closed sets are thereby excluded by the hypothesis
$\rho(F) \geq 1$, but every unbounded $F$ satisfies $\mu(F) = 0$ anyway — two
roots at mutual distance $R$ confine $\{z : |f(z)| < 1\}$ to two discs of
radius $2/R$ — so the formal statement is equivalent to the informal one. For
closed *bounded* (hence compact) $F$ the sequence $d_n(F)$ is the classical one
and converges, so `lim` returns the true transfinite diameter. -/
noncomputable def transfiniteDiameter (F : Set ℂ) : ℝ :=
  lim (atTop.map (fun n => nthTransfiniteDiam F n))

/-- The sublevel set measure $\mu(F, \mu)$: infimum of $\mu(\{z : \|f(z)\| < 1\})$ over
all monic polynomials with roots in $F$. Uses `Fin (n+1)` to ensure at least
one root. -/
noncomputable def sublevelMeasure (F : Set ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (z : Fin (n + 1) → ℂ) (_ : ∀ i, z i ∈ F),
    μ {w : ℂ | ‖(univ : Finset (Fin (n + 1))).prod (fun i => w - z i)‖ < 1}

/--
Erdős Problem 1040 [EHP58, p.135]:

Is it true that for every closed infinite set $F \subseteq \mathbb{C}$ with transfinite
diameter $\geq 1$, the infimum of the Lebesgue measure of $\{z : |f(z)| < 1\}$
over monic polynomials with all roots in $F$ is zero?

This is the "in particular" question of the problem; for the first question —
whether $\mu(F)$ is determined by the transfinite diameter of $F$ — see
`erdos_1040.variants.determined_by_diameter`. The statement quantifies over an
arbitrary additive Haar measure on $\mathbb{C}$, which is equivalent to the
Lebesgue statement since Haar measure is unique up to a positive scalar.
-/
@[category research open, AMS 28 30]
theorem erdos_1040 : answer(sorry) ↔
    ∀ (F : Set ℂ), IsClosed F → F.Infinite → transfiniteDiameter F ≥ 1 →
    ∀ (μ : Measure ℂ) [μ.IsAddHaarMeasure], sublevelMeasure F μ = 0 := by
  sorry

/--
Erdős Problem 1040, partial result [EHP58]:

Erdős, Herzog, and Piranian showed that the answer to Problem 1040 is affirmative
when $F$ is a closed disc or a line segment with transfinite diameter $\geq 1$.
That is, for such $F$, the infimum $\mu(F) = 0$.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.disc (c : ℂ) (r : ℝ) (hr : r > 0)
    (hd : transfiniteDiameter (Metric.closedBall c r) ≥ 1) :
    ∀ (μ : Measure ℂ) [μ.IsAddHaarMeasure],
    sublevelMeasure (Metric.closedBall c r) μ = 0 := by
  sorry

/--
Erdős Problem 1040, partial result [EHP58]:

Erdős, Herzog, and Piranian showed that $\mu(F) = 0$ when $F$ is a line segment
(i.e., a closed interval in $\mathbb{C}$) with transfinite diameter $\geq 1$.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.segment (a b : ℂ) (hab : a ≠ b)
    (hd : transfiniteDiameter (Set.image (fun t : ℝ => (1 - ↑t) * a + ↑t * b) (Set.Icc 0 1)) ≥ 1) :
    ∀ (μ : Measure ℂ) [μ.IsAddHaarMeasure],
    sublevelMeasure (Set.image (fun t : ℝ => (1 - ↑t) * a + ↑t * b) (Set.Icc 0 1)) μ = 0 := by
  sorry

/--
Erdős Problem 1040, partial result [EHP58]:

Erdős, Herzog, and Piranian showed that if the transfinite diameter of $F$ is $< 1$
then $\{z : |f(z)| < 1\}$ always contains a disc of radius $\gg_F 1$: there is a
$\delta = \delta(F) > 0$ such that for every monic polynomial with all roots in $F$
the sublevel set contains an open disc of radius $\delta$.

The boundedness hypothesis is required by the encoding: `transfiniteDiameter`
assigns the junk value $0$ (not $\infty$) to unbounded sets, and for unbounded $F$
the conclusion is genuinely false — two roots at mutual distance $R$ confine
$\{z : |f(z)| < 1\}$ to two discs of radius $2/R$, so no uniform $\delta$ exists.
Informally the hypothesis $\rho(F) < 1$ already excludes unbounded sets.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.small_diameter_disc (F : Set ℂ) (hF : IsClosed F)
    (hFinf : F.Infinite) (hFb : Bornology.IsBounded F)
    (hd : transfiniteDiameter F < 1) :
    ∃ δ : ℝ, δ > 0 ∧ ∀ (n : ℕ) (z : Fin (n + 1) → ℂ), (∀ i, z i ∈ F) →
      ∃ w : ℂ, Metric.ball w δ ⊆
        {v : ℂ | ‖(univ : Finset (Fin (n + 1))).prod (fun i => v - z i)‖ < 1} := by
  sorry

/--
Erdős Problem 1040, related result [ErNe73]:

Erdős and Netanyahu proved that if $F$ is also bounded and connected, with
transfinite diameter $0 < c < 1$, then $\{z : |f(z)| < 1\}$ always contains a
disc of radius $\gg_c 1$: for each such $c$ there is a $\delta = \delta(c) > 0$,
depending only on $c$, such that for every closed, infinite, bounded, connected
$F$ of transfinite diameter $c$ and every monic polynomial with all roots in
$F$, the sublevel set contains an open disc of radius $\delta$.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.erdos_netanyahu (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ δ : ℝ, δ > 0 ∧ ∀ F : Set ℂ, IsClosed F → F.Infinite → Bornology.IsBounded F →
      IsConnected F → transfiniteDiameter F = c →
      ∀ (n : ℕ) (z : Fin (n + 1) → ℂ), (∀ i, z i ∈ F) →
        ∃ w : ℂ, Metric.ball w δ ⊆
          {v : ℂ | ‖(univ : Finset (Fin (n + 1))).prod (fun i => v - z i)‖ < 1} := by
  sorry

/--
Erdős Problem 1040, first question [EHP58, p.135], solved by Aletheia [Fe26]:

Is $\mu(F)$ determined by the transfinite diameter of $F$? That is, is there a
function $g$ with $\mu(F) = g(\rho(F))$ for every closed infinite
$F \subseteq \mathbb{C}$? Here $\mu(F)$ is taken with respect to Lebesgue
measure (`volume`) on $\mathbb{C}$.

Aletheia [Fe26] showed the answer is **no**: see
`erdos_1040.variants.not_determined` for the witnessing construction. Hence
`answer(False)`.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.determined_by_diameter : answer(False) ↔
    ∃ g : ℝ → ℝ≥0∞, ∀ F : Set ℂ, IsClosed F → F.Infinite →
      sublevelMeasure F volume = g (transfiniteDiameter F) := by
  sorry

/--
Erdős Problem 1040, negative result [Fe26]:

Aletheia produced two distinct closed infinite sets $F_1$ and $F_2$, both of
transfinite diameter $0$, such that $\mu(F_1) \geq \pi/4$ while $\mu(F_2)$ can
be made arbitrarily close to $0$ (with respect to Lebesgue measure on
$\mathbb{C}$). In particular $\mu(F)$ is not determined by the transfinite
diameter of $F$.
-/
@[category research solved, AMS 28 30]
theorem erdos_1040.variants.not_determined :
    (∃ F : Set ℂ, IsClosed F ∧ F.Infinite ∧ transfiniteDiameter F = 0 ∧
      ENNReal.ofReal (Real.pi / 4) ≤ sublevelMeasure F volume) ∧
    (∀ ε : ℝ, 0 < ε → ∃ F : Set ℂ, IsClosed F ∧ F.Infinite ∧
      transfiniteDiameter F = 0 ∧ sublevelMeasure F volume < ENNReal.ofReal ε) := by
  sorry

end Erdos1040
