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
# Erdős Problem 401

*Reference:* [erdosproblems.com/401](https://www.erdosproblems.com/401)

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number
theory_. Monographies de L'Enseignement Mathematique (1980).
-/

open Filter

open scoped BigOperators

namespace Erdos401

/--
Erdős Problem 401 [ErGr80, p.78]:

There exists a function $f : \mathbb{N} \to \mathbb{R}$ with $f(r) \to \infty$ as $r \to \infty$,
such that for every $r$, there are infinitely many $n$ for which there exist $a_1, a_2 \in \mathbb{N}$
with $a_1! \cdot a_2! \mid n! \cdot p_1^n \cdot p_2^n \cdots p_r^n$ and
$a_1 + a_2 > n + f(r) \cdot \log n$.
-/
@[category research solved, AMS 11]
theorem erdos_401 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ r : ℕ, {n : ℕ | ∃ a₁ a₂ : ℕ,
        (a₁.factorial * a₂.factorial) ∣
          (n.factorial * ∏ i ∈ Finset.range r, (Nat.nth Nat.Prime i) ^ n) ∧
        ((a₁ + a₂ : ℕ) : ℝ) > (n : ℝ) + f r * Real.log (n : ℝ)}.Infinite := by
  sorry

end Erdos401
