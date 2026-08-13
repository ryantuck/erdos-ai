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
# Erdős Problem 1002

*Reference:* [erdosproblems.com/1002](https://www.erdosproblems.com/1002)

For any $0 < \alpha < 1$, let
$$f(\alpha, n) = \frac{1}{\log n} \sum_{1 \le k \le n} \left(\frac{1}{2} - \{\alpha k\}\right)$$
where $\{\cdot\}$ denotes the fractional part.

Does $f(\alpha, n)$ have an asymptotic distribution function? In other words, is there
a non-decreasing function $g$ such that $g(-\infty) = 0$, $g(\infty) = 1$, and
$$\lim_{n \to \infty} |\{\alpha \in (0,1) : f(\alpha,n) \le c\}| = g(c)$$
where $|\cdot|$ denotes Lebesgue measure?

Kesten [Ke60] proved the analogous result with an additional shift $\beta$:
if $f(\alpha, \beta, n) = \frac{1}{\log n} \sum_{1 \le k \le n} \left(\frac{1}{2} - \{\beta + \alpha k\}\right)$,
then $f(\alpha, \beta, n)$ has asymptotic distribution function
$g(c) = \frac{1}{\pi} \int_{-\infty}^{\rho c} \frac{1}{1+t^2} \, dt$
where $\rho > 0$ is an explicit constant.

As of February 2026, erdosproblems.com lists this problem as open ("cannot be
resolved with a finite computation").

[Er64b] Erdős, P., _Some problems in number theory_. 1964. (Title per the [Er64b]
entry used elsewhere in this repository; full bibliographic details per
erdosproblems.com/latex/1002.)

[Ke60] Kesten, H., 1960. (Bibliographic details per erdosproblems.com/1002.)
-/

open Finset Filter MeasureTheory

namespace Erdos1002

/-- The function $f(\alpha, n) = \frac{1}{\log n} \sum_{k=1}^{n} \left(\frac{1}{2} - \{\alpha k\}\right)$,
where $\{\cdot\}$ denotes the fractional part. -/
noncomputable def erdosF (α : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2 - Int.fract (α * ↑k))) / Real.log ↑n

/--
Erdős Problem 1002 [Er64b]:

Does the function $f(\alpha, n) = \frac{1}{\log n} \sum_{k=1}^n \left(\frac{1}{2} - \{\alpha k\}\right)$
have an asymptotic distribution function? That is, is there a non-decreasing function
$g : \mathbb{R} \to \mathbb{R}$ with $g(-\infty) = 0$ and $g(\infty) = 1$ such that for every
$c \in \mathbb{R}$,
$$\lim_{n \to \infty} \mu(\{\alpha \in (0,1) : f(\alpha,n) \le c\}) = g(c)$$
where $\mu$ is Lebesgue measure.
-/
@[category research open, AMS 11 28]
theorem erdos_1002 : answer(sorry) ↔
    ∃ g : ℝ → ℝ, Monotone g ∧
    Tendsto g atBot (nhds 0) ∧
    Tendsto g atTop (nhds 1) ∧
    ∀ c : ℝ, Tendsto
      (fun n : ℕ =>
        (volume (Set.Ioo (0 : ℝ) 1 ∩ {α : ℝ | erdosF α n ≤ c})).toReal)
      atTop (nhds (g c)) := by
  sorry

/-- The shifted function
$f(\alpha, \beta, n) = \frac{1}{\log n} \sum_{1 \le k \le n} \left(\frac{1}{2} - \{\beta + \alpha k\}\right)$
considered by Kesten [Ke60]. -/
noncomputable def erdosFShifted (α β : ℝ) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, ((1 : ℝ) / 2 - Int.fract (β + α * ↑k))) / Real.log ↑n

/--
Kesten [Ke60] proved the analogue of the main problem for the shifted function
$f(\alpha, \beta, n)$, averaging over the pair $(\alpha, \beta) \in (0,1)^2$
(two-dimensional Lebesgue measure): $f(\alpha, \beta, n)$ has an asymptotic
distribution function, explicitly the Cauchy law
$g(c) = \frac{1}{\pi} \int_{-\infty}^{\rho c} \frac{1}{1+t^2} \, dt$ for an explicit
constant $\rho > 0$. This variant formalizes the existence form of the statement;
the explicit Cauchy form of $g$ is recorded here but not formalized. The source page
does not spell out the underlying measure space; the unit square is the standard
reading of Kesten's theorem.
-/
@[category research solved, AMS 11 28]
theorem erdos_1002.variants.kesten_shifted :
    ∃ g : ℝ → ℝ, Monotone g ∧
    Tendsto g atBot (nhds 0) ∧
    Tendsto g atTop (nhds 1) ∧
    ∀ c : ℝ, Tendsto
      (fun n : ℕ =>
        (volume ((Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1) ∩
          {p : ℝ × ℝ | erdosFShifted p.1 p.2 n ≤ c})).toReal)
      atTop (nhds (g c)) := by
  sorry

end Erdos1002
