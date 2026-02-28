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
# Erdős Problem 363

*Reference:* [erdosproblems.com/363](https://www.erdosproblems.com/363)

Is it true that there are only finitely many collections of disjoint intervals
$I_1, \ldots, I_n$ of consecutive integers with $|I_i| \geq 4$ for all $i$, such that
$\prod_i \prod_{m \in I_i} m$ is a perfect square?

This was disproved:
- [Ul05] Ulas proved infinitely many solutions exist when $n = 4$ or $n \geq 6$, $|I_i| = 4$.
- [BaBe07] Bauer and Bennett proved the same for $n = 3$ and $n = 5$, $|I_i| = 4$.
- [BeVL12] Bennett and Van Luijk found infinitely many solutions for $n \geq 5$, $|I_i| = 5$.
-/

namespace Erdos363

/-- The product of $4$ consecutive natural numbers starting at $a$. -/
def prod4 (a : ℕ) : ℕ := a * (a + 1) * (a + 2) * (a + 3)

/--
Erdős Problem 363 (Disproved by Bauer–Bennett [BaBe07]):

For any $N$, there exist starting points $a, b, c > N$ with $a + 4 \leq b$ and $b + 4 \leq c$
(so the three intervals $\{a, \ldots, a+3\}$, $\{b, \ldots, b+3\}$, $\{c, \ldots, c+3\}$ are
pairwise disjoint) such that the product of all $12$ elements is a perfect square.
-/
@[category research solved, AMS 11]
theorem erdos_363 :
    ∀ N : ℕ, ∃ a b c : ℕ,
      N < a ∧ a + 4 ≤ b ∧ b + 4 ≤ c ∧
      IsSquare (prod4 a * prod4 b * prod4 c) := by
  sorry

end Erdos363
