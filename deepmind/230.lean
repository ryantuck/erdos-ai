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
# Erdős Problem 230

*Reference:* [erdosproblems.com/230](https://www.erdosproblems.com/230)

Let $P(z) = \sum_{k=1}^{n} a_k z^k$ with $a_k \in \mathbb{C}$ and $|a_k| = 1$ for all $k$.
Does there exist a constant $c > 0$ such that, for $n \geq 2$,
$$\max_{|z|=1} |P(z)| \geq (1+c)\sqrt{n}?$$

The lower bound of $\sqrt{n}$ is trivial from Parseval's theorem.

DISPROVED: Kahane [Ka80] constructed 'ultraflat' polynomials with unimodular
coefficients such that $|P(z)| = (1+o(1))\sqrt{n}$ uniformly on the unit circle.
Bombieri and Bourgain [BoBo09] later improved the error term.

[Er57] Erdős, P.

[Er61] Erdős, P.

[Er80h] Erdős, P.

[Ka80] Kahane, J.-P.

[BoBo09] Bombieri, E. and Bourgain, J.
-/

open Finset BigOperators

namespace Erdos230

/--
Erdős Problem 230 [Er57, Er61, Er80h] (DISPROVED):

The original conjecture asked whether there exists $c > 0$ such that every
polynomial $P(z) = \sum_{k=1}^{n} a_k z^k$ with unimodular coefficients
($|a_k| = 1$) satisfies $\max_{|z|=1} |P(z)| \geq (1+c)\sqrt{n}$.

Kahane [Ka80] disproved this by constructing 'ultraflat' polynomials where
$|P(z)| = (1+o(1))\sqrt{n}$ uniformly on the unit circle.

Formalized as the negation: for every $\varepsilon > 0$ and all sufficiently large $n$,
there exists a polynomial with unimodular coefficients whose maximum modulus
on the unit circle is at most $(1 + \varepsilon)\sqrt{n}$.
-/
@[category research solved, AMS 42]
theorem erdos_230 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∃ a : Fin n → ℂ,
      (∀ k : Fin n, ‖a k‖ = 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖∑ k : Fin n, a k * z ^ (k.val + 1)‖ ≤ (1 + ε) * Real.sqrt ↑n := by
  sorry

end Erdos230
