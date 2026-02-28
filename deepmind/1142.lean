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
# Erdős Problem 1142

*Reference:* [erdosproblems.com/1142](https://www.erdosproblems.com/1142)

[Va99] Vaughan, R.C., *Some problems of Erdős in combinatorial number theory*, 1999.
-/

open Nat

namespace Erdos1142

/--
A natural number $n$ has the property that $n - 2^k$ is prime
for every $k \geq 1$ with $2^k < n$.
-/
def AllPowerOfTwoComplementsPrime (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → 2 ^ k < n → (n - 2 ^ k).Prime

/--
Erdős Problem #1142 [Va99, 1.7]:

Are there infinitely many $n$ such that $n - 2^k$ is prime for all $1 < 2^k < n$?

The only known such $n$ are $4, 7, 15, 21, 45, 75, 105$ (OEIS A039669).
Mientka and Weitzenkamp proved there are no other such $n \leq 2^{44}$.
Vaughan proved the count of such $n \leq N$ is at most
$$\exp\left(-c \cdot \frac{\log \log \log N}{\log \log N} \cdot \log N\right) \cdot N$$
for some $c > 0$.
-/
@[category research open, AMS 11]
theorem erdos_1142 :
    answer(sorry) ↔ ∀ N : ℕ, ∃ n : ℕ, n > N ∧ AllPowerOfTwoComplementsPrime n := by
  sorry

end Erdos1142
