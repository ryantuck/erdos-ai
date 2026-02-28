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
# Erdős Problem 381

*Reference:* [erdosproblems.com/381](https://www.erdosproblems.com/381)

[Er44] Erdős, P., _On highly composite numbers_, J. London Math. Soc. 19 (1944), 130–133.

[Ni71] Nicolas, J.-L., _Répartition des nombres hautement composés de Ramanujan_, Canad. J. Math. 23 (1971), 116–130.
-/

open Classical Finset Real

namespace Erdos381

/-- A natural number $n$ is highly composite if every smaller positive natural
number has strictly fewer divisors. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → (Nat.divisors m).card < (Nat.divisors n).card

/-- `highlyCompositeCount x` counts the number of highly composite numbers in $[1, x]$. -/
noncomputable def highlyCompositeCount (x : ℕ) : ℕ :=
  ((Finset.range x).filter (fun n => IsHighlyComposite (n + 1))).card

/--
Erdős Problem 381 (Disproved) [Er44]:

A number $n$ is highly composite if $\tau(m) < \tau(n)$ for all $m < n$, where $\tau(m)$
counts the number of divisors of $m$. Let $Q(x)$ count the number of highly
composite numbers in $[1, x]$.

Erdős asked whether $Q(x) \gg_k (\log x)^k$ for every $k \geq 1$.

Erdős [Er44] proved $Q(x) \gg (\log x)^{1+c}$ for some constant $c > 0$.

The answer is no: Nicolas [Ni71] proved that $Q(x) \ll (\log x)^{O(1)}$,
i.e., there exist constants $C$ and $K$ such that $Q(x) \leq C \cdot (\log x)^K$
for all sufficiently large $x$.

We formalize Nicolas's result, which is the true (negative) answer.
-/
@[category research solved, AMS 11]
theorem erdos_381 :
    ∃ (C K : ℝ), 0 < C ∧ 0 < K ∧
      ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
        (highlyCompositeCount x : ℝ) ≤ C * (Real.log (x : ℝ)) ^ K := by
  sorry

end Erdos381
