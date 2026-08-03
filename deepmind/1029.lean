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
import FormalConjecturesForMathlib.Combinatorics.Ramsey

/-!
# Erdős Problem 1029

*Reference:* [erdosproblems.com/1029](https://www.erdosproblems.com/1029)

If $R(k)$ is the diagonal Ramsey number for $K_k$, the minimal $n$ such that every
2-colouring of the edges of $K_n$ contains a monochromatic copy of $K_k$, then
$$
  R(k) / (k \cdot 2^{k/2}) \to \infty.
$$

The problem is open. In [Er93] Erdős offers \$100 for a proof of this and \$1000 for a
disproof, but says "this last offer is to some extent phoney: I am sure that [this] is
true (but I have been wrong before)."

Erdős and Szekeres [ErSz35] proved $k \cdot 2^{k/2} \ll R(k) \leq \binom{2k-1}{k-1}$.
The probabilistic method gives $R(k) \geq (1+o(1)) \cdot \frac{1}{\sqrt{2}\, e} \cdot k \cdot 2^{k/2}$,
improved by Spencer [Sp75] to $R(k) \geq (1+o(1)) \cdot \frac{\sqrt{2}}{e} \cdot k \cdot 2^{k/2}$.

See also Erdős Problem 77 ([erdosproblems.com/77](https://www.erdosproblems.com/77)) for a
more general problem concerning $\lim_k R(k)^{1/k}$ and discussion of upper bounds for $R(k)$.

[ErSz35] Erdős, P. and Szekeres, G., *A combinatorial problem in geometry*, Compositio Math. 2 (1935), 463–470.

[Sp75] Spencer, J., *Ramsey's theorem — a new lower bound*, J. Combin. Theory Ser. A 18 (1975), 108–115.

[Er93] Erdős, P., *On some of my favourite theorems*. Combinatorics, Paul Erdős is eighty,
Vol. 2 (Keszthely, 1993), 97–132.
-/

open Combinatorics

namespace Erdos1029

/--
Erdős Problem 1029 [Er93, p.337]:

$R(k) / (k \cdot 2^{k/2}) \to \infty$ as $k \to \infty$.

Formulated as: for every $C > 0$, there exists $K_0$ such that for all $k \geq K_0$,
$R(k) \geq C \cdot k \cdot 2^{k/2}$.

Here $R(k)$ is the diagonal Ramsey number, expressed as `hypergraphRamsey 2 k`.
-/
@[category research open, AMS 5]
theorem erdos_1029 :
    ∀ C : ℝ, C > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (hypergraphRamsey 2 k : ℝ) ≥ C * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
  sorry

/--
The lower bound from the source page's remarks: $k \cdot 2^{k/2} \ll R(k)$ [ErSz35],
with the implied constant later improved by Spencer [Sp75] to $(1+o(1))\sqrt{2}/e$.
Stated with a single constant $c > 0$ valid for all $k \geq 1$; this is equivalent to
the eventual (Vinogradov $\ll$) form because $R(k) \geq 1 > 0$ for every $k \geq 1$, so
the finitely many initial values of $k$ only shrink the admissible constant.
-/
@[category research solved, AMS 5]
theorem erdos_1029.variants.lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, 1 ≤ k →
      (hypergraphRamsey 2 k : ℝ) ≥ c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by
  sorry

/--
The upper bound from the source page's remarks: $R(k) \leq \binom{2k-1}{k-1}$, proved by
Erdős and Szekeres [ErSz35] (whose bound $R(k) \leq \binom{2k-2}{k-1}$ is in fact
slightly stronger). The hypothesis $1 \leq k$ keeps the ℕ subtractions $2k - 1$ and
$k - 1$ away from truncation; at $k = 0$ the inequality also holds ($R(0) = 0 \leq 1$)
but the truncated binomial no longer denotes the intended expression.
-/
@[category research solved, AMS 5]
theorem erdos_1029.variants.upper_bound :
    ∀ k : ℕ, 1 ≤ k → hypergraphRamsey 2 k ≤ (2 * k - 1).choose (k - 1) := by
  sorry

end Erdos1029
