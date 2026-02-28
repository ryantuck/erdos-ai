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
# Erdős Problem 154

*Reference:* [erdosproblems.com/154](https://www.erdosproblems.com/154)

[ESS94] Erdős, P., Sárközy, A., and Sós, V. T., 1994.

[Li98] Lindström, B., 1998.

[Ko99] Kolountzakis, M., 1999.
-/

open Filter

open scoped Topology Real

namespace Erdos154

/-- A finite set of natural numbers is a Sidon set (also called a $B_2$ set) if all
pairwise sums $a + b$ (allowing $a = b$) are distinct: whenever $a + b = c + d$
with $a, b, c, d \in A$, we have $\{a, b\} = \{c, d\}$ as multisets. Equivalently,
all differences $a - b$ with $a \neq b$ and $a, b \in A$ are distinct. -/
def IsSidonSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The sumset $A + A = \{a + b \mid a, b \in A\}$. -/
def sumset (A : Finset ℕ) : Finset ℕ := Finset.image₂ (· + ·) A A

/-- The fraction of elements in a finite set of naturals that are congruent to $r$ modulo $m$. -/
noncomputable def modFraction (m r : ℕ) (S : Finset ℕ) : ℝ :=
  ((S.filter (fun n => n % m = r)).card : ℝ) / (S.card : ℝ)

/--
Erdős Problem \#154 [ESS94]:

Let $A \subset \{1, \ldots, N\}$ be a Sidon set with $|A| \sim N^{1/2}$. Must $A + A$ be
well-distributed over all small moduli? In particular, must about half
the elements of $A + A$ be even and half odd?

Proved in the affirmative. Lindström [Li98] showed that $A$ itself is
well-distributed modulo small integers (e.g. $|A \cap \{\text{evens}\}| \approx |A|/2$),
subsequently strengthened by Kolountzakis [Ko99]. The extension to $A + A$
follows immediately from the Sidon property: if $A$ has $e$ even and $o$ odd
elements, then $A + A$ has exactly $e(e+1)/2 + o(o+1)/2$ even elements
and $eo$ odd elements (all distinct by the Sidon property), and the
distribution is approximately $1/2$ each when $e \approx o \approx |A|/2$.

Formalized as: for any sequence $(A_n)_n$ of Sidon sets $A_n \subset \{0, \ldots, n\}$
with $|A_n| / \sqrt{n} \to 1$ as $n \to \infty$, and any fixed modulus $m \geq 1$ and
residue $0 \leq r < m$, the fraction of elements of $A_n + A_n$ in residue
class $r \bmod m$ tends to $1/m$.
-/
@[category research solved, AMS 5 11]
theorem erdos_154 :
    ∀ (A : ℕ → Finset ℕ),
      (∀ n, IsSidonSet (A n)) →
      (∀ n, (A n) ⊆ Finset.range (n + 1)) →
      Tendsto (fun n => ((A n).card : ℝ) / Real.sqrt n) atTop (𝓝 1) →
      ∀ (m : ℕ), 1 ≤ m →
        ∀ r < m,
          Tendsto (fun n => modFraction m r (sumset (A n))) atTop (𝓝 (1 / (m : ℝ))) := by
  sorry

end Erdos154
