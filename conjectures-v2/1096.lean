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
# Erdős Problem 1096

*Reference:* [erdosproblems.com/1096](https://www.erdosproblems.com/1096)

For $1 < q < 1 + \varepsilon$ with $\varepsilon$ sufficiently small, consider the sums
$\sum_{i \in S} q^i$ over all finite $S \subseteq \mathbb{N}$, ordered by size. Is it true
that the gaps between consecutive elements tend to zero?

A problem of Erdős and Joó posed in the 1991 problem session of Great Western Number
Theory [GWNT91]. The problem is **open** (erdosproblems.com, page edition 19 October
2025). The sequence always begins $0, 1, q$.

Known partial results (from the problem page):

- Erdős, Joó, and Komornik [EJK90] proved that no Pisot–Vijayaraghavan number $q$ can
  have this property, and also that for any $1 < q \leq 2$ one has
  $x_{k+1} - x_k \leq 1$ for all $k$.
- Erdős and Joó speculate that the threshold may be $q_0 \approx 1.3247$, the real root
  of $x^3 = x + 1$ and the smallest Pisot–Vijayaraghavan number.
- Bugeaud [Bu96] proved that $1 < q \leq 2$ is a Pisot–Vijayaraghavan number if and only
  if $\liminf_k (x_{k+1}^m - x_k^m) > 0$ for all $m \geq 1$, where $x_k^m$ enumerates the
  numbers expressible as finite sums $\sum_{n \geq 0} c_n q^n$ with
  $c_n \in \{0, \ldots, m\}$ (the sequence in the question being $x_k^1$).
- Erdős, Joó, and Schnitzer [EJS96] improved this: for $1 < q < (1+\sqrt{5})/2$, $q$ is a
  Pisot–Vijayaraghavan number if and only if $\liminf_k (x_{k+1}^2 - x_k^2) > 0$.

[EJK90] Erdős, P., Joó, I., and Komornik, V., *Characterization of the unique expansions
$1 = \sum q^{-n_i}$ and related problems*, Bull. Soc. Math. France (1990), 377–390.

[GWNT91] Great Western Number Theory Problem Session (1991).

[Bu96] Bugeaud, Y., *On a property of Pisot numbers and related questions*, Acta Math.
Hungar. (1996), 33–39.

[EJS96] Erdős, P., Joó, I., and Schnitzer, F. J., *On Pisot numbers*, Ann. Univ. Sci.
Budapest. Eötvös Sect. Math. (1996), 95–99.
-/

open Finset

namespace Erdos1096

/-- The set of all numbers expressible as $\sum_{i \in S} q^i$ for some finite set
$S \subseteq \mathbb{N}$. -/
noncomputable def powerSumSet (q : ℝ) : Set ℝ :=
  {x : ℝ | ∃ S : Finset ℕ, x = S.sum (fun i => q ^ i)}

/--
Erdős Problem 1096 [EJK90, GWNT91]:

Let $1 < q < 1 + \varepsilon$ and consider the set of numbers of the form $\sum_{i \in S} q^i$
(for all finite $S \subseteq \mathbb{N}$), ordered by size as $0 = x_1 < x_2 < \cdots$.

Is it true that, provided $\varepsilon > 0$ is sufficiently small, $x_{k+1} - x_k \to 0$?

Equivalently: there exists $\varepsilon > 0$ such that for all $q \in (1, 1+\varepsilon)$, the
gaps between consecutive elements of the power sum set tend to zero. We formalize this as:
for every $\delta > 0$, every sufficiently large element of the set has a successor
in the set within distance $\delta$.

Erdős and Joó speculate that the threshold may be $q_0 \approx 1.3247$, the real root
of $x^3 = x + 1$, i.e., the smallest Pisot–Vijayaraghavan number. Erdős, Joó, and
Komornik [EJK90] proved that no Pisot–Vijayaraghavan number has this property (so the
threshold cannot exceed $q_0$), and that for $1 < q \leq 2$ the gaps satisfy
$x_{k+1} - x_k \leq 1$ for all $k$.

Note: for any $q > 1$ the power sum set is locally finite (only finitely many finite
subsets have sum below any bound) and unbounded, so "some strictly larger element within
$\delta$" is equivalent to "the immediate successor is within $\delta$", and the
formalization is faithful to the gap condition.
-/
@[category research open, AMS 11]
theorem erdos_1096 :
    answer(sorry) ↔
      ∃ ε : ℝ, 0 < ε ∧
        ∀ q : ℝ, 1 < q → q < 1 + ε →
          ∀ δ : ℝ, 0 < δ →
            ∃ M : ℝ, ∀ x ∈ powerSumSet q, M ≤ x →
              ∃ y ∈ powerSumSet q, x < y ∧ y - x < δ := by
  sorry

/--
Erdős, Joó, and Komornik [EJK90] proved that for any $1 < q \leq 2$ the consecutive gaps
satisfy $x_{k+1} - x_k \leq 1$ for all $k$: every element of the power sum set has a
strictly larger element within distance $1$ (equivalently, its immediate successor is
within distance $1$, since the set is locally finite for $q > 1$).
-/
@[category research solved, AMS 11]
theorem erdos_1096.variants.bounded_gaps :
    ∀ q : ℝ, 1 < q → q ≤ 2 →
      ∀ x ∈ powerSumSet q, ∃ y ∈ powerSumSet q, x < y ∧ y - x ≤ 1 := by
  sorry

/--
Erdős and Joó speculate [GWNT91] that the threshold in Erdős Problem 1096 may be
$q_0 \approx 1.3247$, the real root of $x^3 = x + 1$ and the smallest
Pisot–Vijayaraghavan number: for every $q$ with $1 < q < q_0$, the consecutive gaps of
the power sum set tend to zero. (The cubic $x^3 = x + 1$ has a unique real root, which
exceeds $1$, so the hypotheses pin down $q_0$ uniquely.) By [EJK90] no
Pisot–Vijayaraghavan number has the gap property, so the threshold cannot exceed $q_0$;
this variant asserts the complementary speculation.
-/
@[category research open, AMS 11]
theorem erdos_1096.variants.pisot_threshold :
    ∀ q₀ : ℝ, 1 < q₀ → q₀ ^ 3 = q₀ + 1 →
      ∀ q : ℝ, 1 < q → q < q₀ →
        ∀ δ : ℝ, 0 < δ →
          ∃ M : ℝ, ∀ x ∈ powerSumSet q, M ≤ x →
            ∃ y ∈ powerSumSet q, x < y ∧ y - x < δ := by
  sorry

end Erdos1096
