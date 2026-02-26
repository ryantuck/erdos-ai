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
# Erdős Problem 121

*Reference:* [erdosproblems.com/121](https://www.erdosproblems.com/121)

[Er94b] [Er97] [Er97e] [Er98] Erdős, P., various problems papers.

[ESS95] Erdős, P., Sárközy, A. and Sós, V. T., on products of distinct elements of subsets.

[Er38] Erdős, P., on sequences of integers no one of which divides the product of two others
and on some related problems (1938).

[Ta24] Tao, T., on the density of sets avoiding square-product patterns (2024).
-/

open scoped BigOperators

open Filter

namespace Erdos121

/-- A finset $A$ has the property that no $k$ distinct elements have a product that is
a perfect square. -/
def noKSquareProduct (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → B.card = k → ¬IsSquare (∏ b ∈ B, b)

/-- $F(k, N)$ is the size of the largest subset $A$ of $\{1, \ldots, N\}$ such that
no $k$ distinct elements of $A$ have a product that is a perfect square. -/
noncomputable def F (k N : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = m ∧ noKSquareProduct k A}

/--
Erdős Problem #121 [Er94b, Er97, Er97e, Er98] — DISPROVED

Let $F_k(N)$ be the size of the largest $A \subseteq \{1,\ldots,N\}$ such that the product
of no $k$ distinct elements of $A$ is a perfect square.

Conjectured by Erdős, Sós, and Sárközy [ESS95]: Is $F_5(N) = (1 - o(1)) N$?
More generally, is $F_{2k+1}(N) = (1 - o(1)) N$ for all $k \geq 2$?

Background:
- Erdős–Sós–Sárközy [ESS95] proved $F_2(N) = (6/\pi^2 + o(1)) N$ and
  $F_3(N) = (1 - o(1)) N$, and $F_k(N) \asymp N / \log N$ for all even $k \geq 4$.
- Erdős [Er38] proved $F_4(N) = o(N)$ (in particular, density $0$ for $k = 4$).

This was answered in the negative by Tao [Ta24], who proved that for any $k \geq 4$ there
exists a constant $c_k > 0$ such that $F_k(N) \leq (1 - c_k + o(1)) N$. Thus the density
of the largest such set is bounded strictly away from $1$ for all $k \geq 4$, disproving
the conjecture for all odd $k \geq 5$.

The theorem below formalizes Tao's result.
-/
@[category research solved, AMS 5 11]
theorem erdos_121 :
    ∀ k : ℕ, 4 ≤ k →
    ∃ c : ℝ, 0 < c ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N : ℕ in atTop, (F k N : ℝ) ≤ (1 - c + ε) * N := by
  sorry

end Erdos121
