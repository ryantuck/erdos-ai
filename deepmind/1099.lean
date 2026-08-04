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
# Erdős Problem 1099

*Reference:* [erdosproblems.com/1099](https://www.erdosproblems.com/1099)

Let $1 = d_1 < \cdots < d_{\tau(n)} = n$ be the divisors of $n$, and for $\alpha > 1$ let
$$h_\alpha(n) = \sum_i \left(\frac{d_{i+1}}{d_i} - 1\right)^\alpha.$$

Is it true that $\liminf_{n \to \infty} h_\alpha(n) \ll_\alpha 1$?

The problem appears in [Er81h, p.171]. Erdős [Er81h] remarks that $n!$ or
$\mathrm{lcm}\{1, \ldots, n\}$ would be good candidates.
The $\liminf$ is trivially $\geq 1$ (considering the term $i = 1$).

Proved by Vose [Vo84] who constructed a specific sequence achieving bounded $h_\alpha(n)$.
It remains open whether $n!$ or $\mathrm{lcm}\{1, \ldots, n\}$ satisfy this property.

Erdős remarks that this problem occurred to him when considering $\sum_i d_{i+1}/d_i$. One
easily has $\sum_i \frac{d_{i+1}}{d_i} > \tau(n) - 1 + \log n$ (the source states the bound
with $\tau(n)$ in place of $\tau(n) - 1$, but that stronger form fails for
$n \in \{2, 3, 4, 6, 8, 12, 24\}$ — see the `ratio_sum_lower` variant below), and Erdős
asked whether
$$\liminf_{n \to \infty} \left(\sum_i \frac{d_{i+1}}{d_i} - \tau(n) - \log n\right) < \infty,$$
which follows from the affirmative answer to the main question (see the
`ratio_sum_liminf` variant below).

This resembles the function $G(n) = \sum_i d_i / d_{i+1}$ considered in problem \#673.

[Er81h] Erdős, P., _Some problems and results on additive and multiplicative number theory_.
Analytic number theory (Philadelphia, Pa., 1980) (1981), 171–182.

[Vo84] Vose, M. D., _Integers with consecutive divisors in small ratio_, J. Number Theory (1984).
-/

open Classical Finset Real

namespace Erdos1099

/-- The sorted list of divisors of $n$ in increasing order. -/
def sortedDivisors (n : ℕ) : List ℕ :=
  (Nat.divisors n).sort (· ≤ ·)

/-- $h_\alpha(n) = \sum_i (d_{i+1}/d_i - 1)^\alpha$ where $d_1 < \cdots < d_{\tau(n)}$ are the
divisors of $n$ in increasing order. -/
noncomputable def hAlpha (α : ℝ) (n : ℕ) : ℝ :=
  let ds := sortedDivisors n
  ((ds.zip ds.tail).map (fun p => ((p.2 : ℝ) / (p.1 : ℝ) - 1) ^ α)).sum

/--
Erdős Problem 1099 (Proved by Vose [Vo84]):

For every $\alpha > 1$, there exists a constant $C$ (depending on $\alpha$) such that
$h_\alpha(n) \leq C$ for infinitely many $n$, i.e., $\liminf_{n \to \infty} h_\alpha(n)$
is finite.

Formally: for every $\alpha > 1$, there exists $C$ such that for every $N$, there
exists $n \geq N$ with $h_\alpha(n) \leq C$.
-/
@[category research solved, AMS 11]
theorem erdos_1099 : answer(True) ↔
    ∀ α : ℝ, α > 1 → ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ hAlpha α n ≤ C := by
  sorry

/--
Is $h_\alpha(n!)$ bounded for each $\alpha > 1$?

Erdős [Er81h] suggested that $n!$ would be a good candidate for achieving bounded
$h_\alpha$. This remains open.
-/
@[category research open, AMS 11]
theorem erdos_1099_factorial : answer(sorry) ↔
    ∀ α : ℝ, α > 1 → ∃ C : ℝ, ∀ n : ℕ, hAlpha α n.factorial ≤ C := by
  sorry

/--
Is $h_\alpha(\mathrm{lcm}\{1, \ldots, n\})$ bounded for each $\alpha > 1$?

Erdős [Er81h] suggested that $\mathrm{lcm}\{1, \ldots, n\}$ would be a good candidate for
achieving bounded $h_\alpha$. This remains open.
-/
@[category research open, AMS 11]
theorem erdos_1099_lcm : answer(sorry) ↔
    ∀ α : ℝ, α > 1 → ∃ C : ℝ, ∀ n : ℕ, hAlpha α ((Icc 1 n).lcm id) ≤ C := by
  sorry

/--
For every $n \geq 2$,
$$\sum_i \frac{d_{i+1}}{d_i} > \tau(n) - 1 + \log n,$$
where $1 = d_1 < \cdots < d_{\tau(n)} = n$ are the divisors of $n$.

This is the corrected form of the "easy to see" bound stated on the problem page, which
gives $\sum_i \frac{d_{i+1}}{d_i} > \tau(n) + \log n$; that stronger inequality is
literally false for $n \in \{2, 3, 4, 6, 8, 12, 24\}$ (e.g. for $n = 2$ the sum is $2$
while $\tau(2) + \log 2 \approx 2.69$), though these are the only failures up to
$3 \times 10^5$. The corrected bound follows from $r - 1 > \log r$ for $r > 1$ applied to
each ratio $r_i = d_{i+1}/d_i$, since $\sum_i (r_i - 1) > \sum_i \log r_i = \log n$ and
the sum has $\tau(n) - 1$ terms.
-/
@[category research solved, AMS 11]
theorem erdos_1099.variants.ratio_sum_lower (n : ℕ) (hn : 2 ≤ n) :
    ((Nat.divisors n).card : ℝ) - 1 + Real.log n <
      (((sortedDivisors n).zip (sortedDivisors n).tail).map
        (fun p => (p.2 : ℝ) / (p.1 : ℝ))).sum := by
  sorry

/--
Erdős asked whether
$$\liminf_{n \to \infty} \left(\sum_i \frac{d_{i+1}}{d_i} - \tau(n) - \log n\right) < \infty,$$
where $1 = d_1 < \cdots < d_{\tau(n)} = n$ are the divisors of $n$.

The problem page notes this would follow from an affirmative answer to the main question,
which Vose [Vo84] provided; hence the answer is yes. Concretely, writing
$r_i = d_{i+1}/d_i$, one has
$\sum_i r_i - \tau(n) - \log n = \sum_i (r_i - 1 - \log r_i) - 1 \leq h_2(n) - 1$
(using $r - 1 - \log r \leq (r-1)^2$ for $r \geq 1$), so the $\alpha = 2$ case of
`erdos_1099` bounds this quantity along an infinite sequence of $n$.
-/
@[category research solved, AMS 11]
theorem erdos_1099.variants.ratio_sum_liminf : answer(True) ↔
    ∃ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
      (((sortedDivisors n).zip (sortedDivisors n).tail).map
        (fun p => (p.2 : ℝ) / (p.1 : ℝ))).sum
        - ((Nat.divisors n).card : ℝ) - Real.log n ≤ C := by
  sorry

end Erdos1099
