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
# Erdős Problem 205

*Reference:* [erdosproblems.com/205](https://www.erdosproblems.com/205)

[ErGr80] Erdős, P. and Graham, R., *Old and new problems and results in combinatorial number
theory*. Monographies de L'Enseignement Mathematique (1980).
-/

open Real

namespace Erdos205

/--
Erdős Problem 205 (Disproved) [ErGr80, p.28]:

Erdős and Graham asked whether all sufficiently large $n$ can be written as
$2^k + m$ for some $k \geq 0$, where $\Omega(m) < \log(\log(m))$. Here $\Omega(m)$ is the number
of prime divisors of $m$ counted with multiplicity.

This was disproved by Barreto and Leeham. The result was quantified by Tao
and Alexeev: there are infinitely many $n$ such that for all $k$ with $2^k \leq n$,
$n - 2^k$ has at least $\gg (\log n / \log \log n)^{1/2}$ prime factors.

We formalize the negation of the original conjecture, which is the true statement.
-/
@[category research solved, AMS 11]
theorem erdos_205 :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∀ k : ℕ, 2 ^ k ≤ n →
        Real.log (Real.log ((n - 2 ^ k : ℕ) : ℝ)) ≤
          ((n - 2 ^ k).primeFactorsList.length : ℝ) := by
  sorry

end Erdos205
