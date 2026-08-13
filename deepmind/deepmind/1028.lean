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
# Erdős Problem 1028

*Reference:* [erdosproblems.com/1028](https://www.erdosproblems.com/1028)

Let $H(n) = \min_f \max_{X \subseteq \{1,\ldots,n\}} \left|\sum_{x \neq y \in X} f(x,y)\right|$,
where $f$ ranges over all functions $f\colon \{1,\ldots,n\}^2 \to \{-1,1\}$. Estimate $H(n)$.

The problem is posed in [Er63d] and [Er71, p.107]. Erdős [Er63d] proved
$n/4 \le H(n) \ll n^{3/2}$. Erdős and Spencer [ErSp71] proved that $H(n) \gg n^{3/2}$.

Together these give $H(n) = \Theta(n^{3/2})$.

Note: $f$ must be interpreted as ranging over *symmetric* $\pm 1$ functions —
equivalently, $2$-colourings of the edges of the complete graph $K_n$, as in [ErSp71].
If arbitrary functions on ordered pairs were allowed, any antisymmetric choice
($f(x,y) = -f(y,x)$ for $x \neq y$) would make every subset sum vanish and force
$H(n) = 0$, contradicting the proved bound $n/4 \le H(n)$. For symmetric $f$ the sum
over ordered pairs is exactly twice the sum over edges, a factor absorbed by the
$\Theta$-constants.

The problem is listed as SOLVED (LEAN) on erdosproblems.com (resolved, with the
resolution verified in Lean; page accessed 2026-02-22). Tags: graph theory, discrepancy.

[Er63d] Erdős, P., _On combinatorial questions connected with a theorem of Ramsey and van
der Waerden_, Mat. Lapok (1963), 29–37.

[Er71] Erdős, P., _Topics in combinatorial analysis_, Proc. Second Louisiana Conf. on
Combinatorics, Graph Theory and Computing (1971), 2–20.

[ErSp71] Erdős, P., Spencer, J., _Imbalances in k-colorations_, Networks (1971/72), 379–385.
-/

open Finset

namespace Erdos1028

/-- The discrepancy sum of a $\pm 1$ function $f$ over a subset $X$ of $\operatorname{Fin}(n)$:
$\sum_{x \neq y \in X} f(x, y)$ over ordered pairs with $x \neq y$. -/
def discrepancySum (n : ℕ) (f : Fin n → Fin n → ℤ) (X : Finset (Fin n)) : ℤ :=
  X.sum fun x => (X.filter (· ≠ x)).sum fun y => f x y

/--
Erdős Problem 1028 [Er63d] [Er71, p.107]:

$H(n) = \Theta(n^{3/2})$, where
$H(n) = \min_f \max_{X \subseteq \{1,\ldots,n\}} \left|\sum_{x \neq y \in X} f(x,y)\right|$
and $f$ ranges over all *symmetric* $\pm 1$ valued functions on pairs (equivalently,
$2$-colourings of the edges of $K_n$).

This is equivalent to two bounds:
- Lower bound (Erdős–Spencer [ErSp71]): every symmetric $\pm 1$ function $f$ has some
  subset $X$ with discrepancy at least $C_1 \cdot n^{3/2}$.
- Upper bound (Erdős [Er63d]): there exists a symmetric $\pm 1$ function $f$ such that
  all subsets have discrepancy at most $C_2 \cdot n^{3/2}$.

The symmetry hypotheses are essential: without them the antisymmetric function
$f(x,y) = 1$ for $x < y$ and $f(x,y) = -1$ otherwise makes every `discrepancySum`
vanish, falsifying the lower bound (and trivialising the upper bound).
-/
@[category research solved, AMS 5]
theorem erdos_1028 :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    -- Lower bound: every symmetric ±1 function has a subset with large discrepancy
    (∀ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) →
      (∀ i j, f i j = f j i) →
      ∃ X : Finset (Fin n),
        C₁ * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ |(discrepancySum n f X : ℝ)|) ∧
    -- Upper bound: there is a symmetric ±1 function with all discrepancies bounded
    (∃ f : Fin n → Fin n → ℤ, (∀ i j, f i j = 1 ∨ f i j = -1) ∧
      (∀ i j, f i j = f j i) ∧
      ∀ X : Finset (Fin n),
        |(discrepancySum n f X : ℝ)| ≤ C₂ * (n : ℝ) ^ ((3 : ℝ) / 2)) := by
  sorry

/--
Erdős [Er63d] proved the explicit lower bound $n/4 \le H(n)$, stated on the problem
page without restriction on $n$. It is formalized here for $n \ge 2$: at $n = 1$ there
are no pairs $x \neq y$, every discrepancy sum is $0$, and $H(1) = 0 < 1/4$, so the
unrestricted bound is literally false. For $2 \le n \le 8$ the bound already follows
from a single off-diagonal pair $X = \{x, y\}$, whose discrepancy sum is $\pm 2$.
The pair-counting convention matters for the constant: in the unordered (edge) count
one has $H_{\mathrm{edge}}(5) = 1 < 5/4$ (colour a $5$-cycle red and the remaining
edges of $K_5$ blue; every subset then has edge-imbalance at most $1$), so at small $n$
the page's $n/4$ bound holds only in the ordered-pair count used by `discrepancySum`.
-/
@[category research solved, AMS 5]
theorem erdos_1028.variants.linear_lower_bound (n : ℕ) (hn : 2 ≤ n)
    (f : Fin n → Fin n → ℤ) (hpm : ∀ i j, f i j = 1 ∨ f i j = -1)
    (hsymm : ∀ i j, f i j = f j i) :
    ∃ X : Finset (Fin n), (n : ℝ) / 4 ≤ |(discrepancySum n f X : ℝ)| := by
  sorry

end Erdos1028
