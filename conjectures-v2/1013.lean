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
# Erdős Problem 1013

Let $h_3(k)$ be the minimal $n$ such that there exists a triangle-free graph on $n$ vertices
with chromatic number $k$. Find an asymptotic for $h_3(k)$, and also prove
$$\lim_{k\to \infty}\frac{h_3(k+1)}{h_3(k)}=1.$$

The problem is OPEN (source page edition 21 January 2026, accessed 2026-02-22). The limit
statement is formalized as `erdos_1013`; the request for an asymptotic formula is open-ended
(no conjectured formula is stated on the source page) and is not directly formalized, but the
known partial results are recorded as variants below.

The function $h_3(k)$ is dual to the function $f(n)$ considered in Problem #1104 (the maximum
chromatic number of a triangle-free graph on $n$ vertices), in that $h_3(k) = n$ if and only
if $n$ is minimal such that $f(n) = k$. Graver and Yackel [GrYa68] proved
$h_3(k) \gg \frac{\log k}{\log\log k}k^2$. The source page states that the bounds
$(1-o(1))(n/\log n)^{1/2} \leq f(n) \leq (2+o(1))(n/\log n)^{1/2}$ from Problem #1104 imply
$$\left(\frac{1}{2}-o(1)\right)k^2\log k\leq h_3(k) \leq (1+o(1))k^2\log k;$$
the lower bound follows by inverting the upper bound on $f$, but inverting the stated lower
bound on $f$ yields only $h_3(k) \leq (2+o(1))k^2\log k$ (see
`erdos_1013.variants.upper_bound` for details), so the constant in the page's upper bound
could not be independently verified.

Note that these bounds determine $h_3(k)$ only up to a constant factor and therefore do not
resolve the limit statement.

Related problems: #920 (generalization to $K_r$-free graphs), #1104 (dual formulation).

OEIS: [A292528](https://oeis.org/A292528).

*Reference:* [erdosproblems.com/1013](https://www.erdosproblems.com/1013)

[Er71] Erdős, P., *Some unsolved problems in graph theory and combinatorial analysis*.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969) (1971), 97–109.

[GrYa68] Graver, J., Yackel, J., _Some graph theoretic results associated with Ramsey's theorem_.
Journal of Combinatorial Theory (1968), 125–175.
-/

open SimpleGraph

namespace Erdos1013

/-- $h_3(k)$ is the minimum number of vertices $n$ such that there exists a
triangle-free graph on $n$ vertices with chromatic number exactly $k$. -/
noncomputable def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞)}

/--
Erdős Problem 1013 [Er71]:

$$\lim_{k \to \infty} \frac{h_3(k+1)}{h_3(k)} = 1,$$

where $h_3(k)$ is the minimum number of vertices of a triangle-free graph with
chromatic number $k$.

Formulated as: for every $\varepsilon > 0$, there exists $K_0$ such that for all $k \geq K_0$,
$\left| \frac{h_3(k+1)}{h_3(k)} - 1 \right| \leq \varepsilon$.

Note: the known bounds (see Problem 1104 and the variants below) determine $h_3(k)$ only up
to a constant factor, so they do not resolve this problem. It would follow from an asymptotic
formula $h_3(k) = (c + o(1))k^2 \log k$ for some constant $c > 0$, which is the (open) first
part of the problem.
-/
@[category research open, AMS 5]
theorem erdos_1013 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      |(h3 (k + 1) : ℝ) / (h3 k : ℝ) - 1| ≤ ε := by
  sorry

/--
Graver and Yackel [GrYa68] proved
$$h_3(k) \gg \frac{\log k}{\log\log k}k^2.$$
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.graver_yackel :
    ∃ c : ℝ, c > 0 ∧
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      c * ((k : ℝ) ^ 2 * Real.log (k : ℝ) / Real.log (Real.log (k : ℝ))) ≤ (h3 k : ℝ) := by
  sorry

/--
The lower bound
$$\left(\frac{1}{2}-o(1)\right)k^2\log k \leq h_3(k),$$
which (per the source page) follows from the upper bound
$f(n) \leq (2+o(1))(n/\log n)^{1/2}$ of Davies and Illingworth stated at Problem #1104:
a triangle-free graph with chromatic number $k$ on $n = h_3(k)$ vertices gives
$k \leq (2+o(1))(n/\log n)^{1/2}$, i.e. $n \geq (1/4-o(1))k^2\log n = (1/2-o(1))k^2\log k$.
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.lower_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (1 / 2 - ε) * ((k : ℝ) ^ 2 * Real.log (k : ℝ)) ≤ (h3 k : ℝ) := by
  sorry

/--
The upper bound
$$h_3(k) \leq (2+o(1))k^2\log k.$$
The source page states the stronger bound $h_3(k) \leq (1+o(1))k^2\log k$ as following from
the bounds at Problem #1104, but inverting the lower bound
$f(n) \geq (1-o(1))(n/\log n)^{1/2}$ (Hefty–Horn–King–Pfender) stated there yields only this
weaker constant: from $k = (1-o(1))(n/\log n)^{1/2}$ one gets
$n = (1+o(1))k^2\log n = (2+o(1))k^2\log k$, since $\log n = (2+o(1))\log k$. The safe
$(2+o(1))$ form is formalized here; the page's $(1+o(1))$ claim could not be independently
verified offline.
-/
@[category research solved, AMS 5]
theorem erdos_1013.variants.upper_bound :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (h3 k : ℝ) ≤ (2 + ε) * ((k : ℝ) ^ 2 * Real.log (k : ℝ)) := by
  sorry

end Erdos1013
