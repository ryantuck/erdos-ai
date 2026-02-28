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
# Erdős Problem 1037

*Reference:* [erdosproblems.com/1037](https://www.erdosproblems.com/1037)

Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice,
and the number of distinct degrees is $> (\frac{1}{2} + \varepsilon)n$. Must $G$
contain a trivial (empty or complete) subgraph of size 'much larger' than
$\log n$?

A question of Chen and Erdős [Er93, p.347]. The answer is no — Cambie, Chan,
and Hunter gave a construction of a graph on $n$ vertices with at least
$\frac{3}{4}n$ distinct degrees, every degree appears at most twice, and the
largest trivial subgraph has size $O(\log n)$.

[Er93] Erdős, P., _On some of my favourite theorems_. Combinatorics, Paul Erdős
is eighty, Vol. 2 (Keszthely, 1993), 97-132.
-/

open SimpleGraph Finset

namespace Erdos1037

/--
**Erdős Problem 1037** (Disproved by Cambie, Chan, Hunter) [Er93, p.347]:

The negation of the original conjecture: there exist $\varepsilon > 0$ and
$C > 0$ such that for all sufficiently large $n$, there exists a graph $G$ on
$n$ vertices where every degree occurs at most twice, the number of distinct
degrees is $> (1/2 + \varepsilon) \cdot n$, and yet every clique and every
independent set has size $\leq C \cdot \log n$.

That is, one cannot guarantee a trivial subgraph much larger than $\log n$.
-/
@[category research solved, AMS 5]
theorem erdos_1037 :
    ∃ ε : ℝ, ε > 0 ∧
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ G : SimpleGraph (Fin n),
    ∃ _ : DecidableRel G.Adj,
      -- Every degree occurs at most twice
      (∀ d : ℕ, (Finset.univ.filter (fun v =>
        (Finset.univ.filter (fun w => G.Adj v w)).card = d)).card ≤ 2) ∧
      -- The number of distinct degrees is > (1/2 + ε) · n
      ((Finset.univ.image (fun v =>
        (Finset.univ.filter (fun w => G.Adj v w)).card)).card : ℝ) >
        (1 / 2 + ε) * (n : ℝ) ∧
      -- Every clique has size ≤ C · log n
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) ∧
      -- Every independent set has size ≤ C · log n
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) := by
  sorry

end Erdos1037
