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
# Erdős Problem 241

*Reference:* [erdosproblems.com/241](https://www.erdosproblems.com/241)

Let $f(N)$ be the maximum size of $A \subseteq \{1, \ldots, N\}$ such that the sums $a + b + c$
with $a, b, c \in A$ are all distinct (aside from the trivial coincidences). Is it true
that $f(N) \sim N^{1/3}$?

A set with this property is called a $B_3$ set (or Sidon set of order 3).

Originally asked to Erdős by Bose. Bose and Chowla [BoCh62] proved the lower
bound $(1 + o(1))N^{1/3} \leq f(N)$. The best known upper bound is due to Green [Gr01]:
$f(N) \leq ((7/2)^{1/3} + o(1))N^{1/3}$.

\$100 prize.

[Er61, Er69, Er70b, Er70c, Er73, Er77c, ErGr80] — Various Erdős papers posing and
discussing this problem.

[BoCh62] Bose, R. C. and Chowla, S., _Theorems in the additive theory of numbers_,
Comment. Math. Helv. 37 (1962), 141–147.

[Gr01] Green, B., _The number of squares and $B_h[g]$ sets_, Acta Arith. 100 (2001), 365–390.
-/

open Filter

namespace Erdos241

/-- A finite set $A \subseteq \mathbb{N}$ is a *$B_3$ set* if whenever
$a_1 + a_2 + a_3 = b_1 + b_2 + b_3$ with all elements from $A$ (in sorted order),
then the two triples are identical. Equivalently, all 3-element sums are distinct
up to reordering. -/
def IsB3Set (A : Finset ℕ) : Prop :=
  ∀ a₁ a₂ a₃ b₁ b₂ b₃ : ℕ,
    a₁ ∈ A → a₂ ∈ A → a₃ ∈ A → b₁ ∈ A → b₂ ∈ A → b₃ ∈ A →
    a₁ ≤ a₂ → a₂ ≤ a₃ → b₁ ≤ b₂ → b₂ ≤ b₃ →
    a₁ + a₂ + a₃ = b₁ + b₂ + b₃ →
    a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃

/-- $f(N)$ is the maximum cardinality of a $B_3$ subset of $\{1, \ldots, N\}$. -/
noncomputable def erdos241F (N : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsB3Set A ∧ A.card = k}

/--
Erdős Problem 241 [Er61, Er69, Er70b, Er70c, Er73, Er77c, ErGr80]:
Is it true that $f(N) \sim N^{1/3}$, i.e., the ratio $f(N) / N^{1/3}$ tends to $1$
as $N \to \infty$?

Known bounds:
- $(1 + o(1))N^{1/3} \leq f(N)$ (Bose–Chowla [BoCh62])
- $f(N) \leq ((7/2)^{1/3} + o(1))N^{1/3}$ (Green [Gr01])
-/
@[category research open, AMS 5 11]
theorem erdos_241 : answer(sorry) ↔
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop,
        (1 - ε) * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (erdos241F N : ℝ) ∧
        (erdos241F N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) := by
  sorry

end Erdos241
