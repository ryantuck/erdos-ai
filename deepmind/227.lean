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
# Erdős Problem 227

*Reference:* [erdosproblems.com/227](https://www.erdosproblems.com/227)

[ClHa64] Clunie, J. and Hayman, W. K., *The spherical derivative of integral and
meromorphic functions*, Comment. Math. Helv. 40 (1966), 117-148.
-/

open Complex Filter

open scoped Topology

namespace Erdos227

/--
The maximum term of a power series with coefficients $a$ at radius $r$:
$\mu(r) = \sup_n \|a_n\| \cdot r^n$
-/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  ⨆ n : ℕ, ‖a n‖ * r ^ n

/--
The maximum modulus of $f$ on the circle of radius $r$:
$M(r) = \sup\{\|f(z)\| \mid \|z\| = r\}$
-/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ x = ‖f z‖}

/--
Erdős Problem 227 (Disproved):
Let $f = \sum a_n z^n$ be an entire function which is not a polynomial. Is it true that if
$$\lim_{r \to \infty} \frac{\max_n |a_n| r^n}{\max_{|z|=r} |f(z)|}$$
exists then it must be $0$?

This was disproved by Clunie and Hayman [ClHa64], who showed that the limit can take
any value in $[0, 1/2]$.
-/
@[category research solved, AMS 30]
theorem erdos_227 : answer(False) ↔
    ∀ (f : ℂ → ℂ) (a : ℕ → ℂ),
      (∀ z : ℂ, HasSum (fun n => a n * z ^ n) (f z)) →
      (∀ N : ℕ, ∃ n, N < n ∧ a n ≠ 0) →
      ∀ L : ℝ, Tendsto (fun r => maxTerm a r / maxModulus f r) atTop (𝓝 L) →
      L = 0 := by
  sorry

end Erdos227
