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
# Erdős Problem 1023

Let $F(n)$ be the maximal size of a family of subsets of $\{1, \ldots, n\}$ such that no set
in this family is the union of other members of the family. Is it true that there is a
constant $c > 0$ such that
$$F(n) \sim c \frac{2^n}{n^{1/2}}?$$

*Reference:* [erdosproblems.com/1023](https://www.erdosproblems.com/1023)

The answer is yes. Erdős and Kleitman proved in unpublished work that
$F(n) \asymp 2^n / \sqrt{n}$. Zach Hunter observes (in the comments on the problem page)
that the full asymptotic follows from the solution to Problem 447 (Kleitman's theorem
[Kl71]), which implies $F(n) \sim \binom{n}{\lfloor n/2 \rfloor}$. As of February 2026,
erdosproblems.com marks this problem SOLVED (LEAN), i.e. the resolution has been formally
verified in Lean.

If one only forbids a set being the union of *two* other members of the family
($A = B \cup C$), this is the subject of Problem 447.

Note: The original source [Er71] contains a typographical error (exponent $3/2$ instead of $1/2$).

Contributors: Stijn Cambie, Zach Hunter.

[Er71] Erdős, P., _Some unsolved problems in graph theory and combinatorial analysis_.
Combinatorial Mathematics and its Applications (Proc. Conf., Oxford, 1969), 1971, pp. 97-109.

[Kl71] Kleitman, D., _Collections of subsets containing no two sets and their union_.
Proc. LA Meeting AMS (1971), 153-155.
-/

open Finset Filter

open scoped Topology

namespace Erdos1023

/-- A family $\mathcal{F}$ of subsets of $\operatorname{Fin}(n)$ is *union-free* if no member of
    $\mathcal{F}$ equals the union of some non-empty sub-collection of other members. -/
def IsUnionFreeFamily {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, ∀ S ⊆ 𝓕.erase A, S.Nonempty → S.sup id ≠ A

/-- $F(n)$ is the maximum cardinality of a union-free family of subsets of
    $\operatorname{Fin}(n)$. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ 𝓕 : Finset (Finset (Fin n)), IsUnionFreeFamily 𝓕 ∧ 𝓕.card = k}

/--
Erdős Problem 1023 [Er71, p. 105]:

Is it true that there is a constant $c > 0$ such that $F(n) \sim c \cdot 2^n / \sqrt{n}$,
where $F(n)$ is the maximum size of a union-free family of subsets of $\{1, \ldots, n\}$?

The answer is yes: Erdős and Kleitman proved $F(n) \asymp 2^n / \sqrt{n}$ in unpublished
work, and Zach Hunter observes that the solution to Problem 447 [Kl71] implies
$F(n) \sim \binom{n}{\lfloor n/2 \rfloor}$, which gives the asymptotic with
$c = \sqrt{2/\pi}$.

The asymptotic is formulated as:
$\lim_{n \to \infty} F(n) \cdot \sqrt{n} \,/\, (c \cdot 2^n) = 1$.
-/
@[category research solved, AMS 5]
theorem erdos_1023 : answer(True) ↔
    ∃ c : ℝ, c > 0 ∧
    Tendsto
      (fun n : ℕ => (unionFreeMax n : ℝ) * Real.sqrt (↑n) / (c * (2 : ℝ) ^ n))
      atTop (nhds 1) := by
  sorry

/--
Stronger form of Erdős Problem 1023, making the connection to Problem 447 explicit
(observed by Zach Hunter, recorded on the problem page):

$F(n) \sim \binom{n}{\lfloor n/2 \rfloor}$, i.e., the ratio $F(n) / \binom{n}{\lfloor n/2 \rfloor}$
tends to $1$. This pins down the constant $c = \sqrt{2/\pi}$ via Stirling's approximation.
-/
@[category research solved, AMS 5]
theorem erdos_1023.variants.central_binomial :
    Tendsto
      (fun n : ℕ => (unionFreeMax n : ℝ) / (Nat.choose n (n / 2) : ℝ))
      atTop (nhds 1) := by
  sorry

/--
Erdős and Kleitman proved in unpublished work that $F(n) \asymp 2^n / \sqrt{n}$
(recorded on the problem page; [Er71] states this with an exponent of $3/2$, presumably
a typo for $1/2$).

Stated for $n \geq 1$: at $n = 0$ the comparison function $2^n / \sqrt{n}$ degenerates
(Lean's division by $\sqrt{0} = 0$ yields $0$, so the upper bound would fail there).
Since $F(n) \cdot \sqrt{n} / 2^n$ is positive and finite for every $n \geq 1$, this
all-$n \geq 1$ form is equivalent to the eventual ($n$ large) form of $\asymp$.
-/
@[category research solved, AMS 5]
theorem erdos_1023.variants.erdos_kleitman :
    ∃ c₁ : ℝ, c₁ > 0 ∧ ∃ c₂ : ℝ, c₂ > 0 ∧ ∀ n : ℕ, 1 ≤ n →
      c₁ * (2 : ℝ) ^ n / Real.sqrt (↑n) ≤ (unionFreeMax n : ℝ) ∧
      (unionFreeMax n : ℝ) ≤ c₂ * (2 : ℝ) ^ n / Real.sqrt (↑n) := by
  sorry

end Erdos1023
