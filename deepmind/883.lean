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
# Erdős Problem 883

*Reference:* [erdosproblems.com/883](https://www.erdosproblems.com/883)

[ErSa97] Erdős, P. and Sárközy, A., on cycles in the coprime graph of integers.
-/

open Finset

namespace Erdos883

/--
The coprimality graph on a subset $A$ of natural numbers: two distinct elements
are connected by an edge if and only if they are coprime ($\gcd = 1$).
-/
def coprimeGraph (A : Finset ℕ) : SimpleGraph ℕ where
  Adj x y := x ∈ A ∧ y ∈ A ∧ x ≠ y ∧ Nat.Coprime x y
  symm := by
    intro x y ⟨hx, hy, hne, hcop⟩
    exact ⟨hy, hx, hne.symm, hcop.symm⟩
  loopless := ⟨fun x ⟨_, _, hne, _⟩ => hne rfl⟩

/--
A graph contains a cycle of length $k$: there exist $k$ distinct vertices
$v_0, \ldots, v_{k-1}$ such that $v_i$ is adjacent to $v_{(i+1) \bmod k}$ for all $i$.
Uses $\mathbb{Z}/k\mathbb{Z}$ for natural cyclic indexing. For $k < 3$ this is vacuously
false due to the loopless/irreflexive properties of simple graphs.
-/
def SimpleGraph.ContainsCycle {α : Type*} (G : SimpleGraph α) (k : ℕ) : Prop :=
  ∃ f : ZMod k → α, Function.Injective f ∧ ∀ i, G.Adj (f i) (f (i + 1))

/--
The threshold function: $\lfloor n/2 \rfloor + \lfloor n/3 \rfloor - \lfloor n/6 \rfloor$,
equal to the count of integers in $\{1, \ldots, n\}$ divisible by $2$ or $3$
(by inclusion-exclusion).
-/
def erdos883Threshold (n : ℕ) : ℕ := n / 2 + n / 3 - n / 6

/--
For $A \subseteq \{1, \ldots, n\}$, let $G(A)$ be the coprimality graph on $A$. If
$|A| > \lfloor n/2 \rfloor + \lfloor n/3 \rfloor - \lfloor n/6 \rfloor$ then $G(A)$
contains all odd cycles of length at most $n/3 + 1$.

A problem of Erdős and Sárközy [ErSa97], who proved this for cycles of
length $\leq cn$ for some constant $c > 0$. The threshold is best possible since
the set of integers in $\{1, \ldots, n\}$ divisible by $2$ or $3$ has this cardinality
and its coprimality graph contains no triangles.
-/
@[category research open, AMS 5 11]
theorem erdos_883 :
    ∀ n : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) →
      A.card > erdos883Threshold n →
      ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → k ≤ n / 3 + 1 →
        (coprimeGraph A).ContainsCycle k := by
  sorry

end Erdos883
