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

import FormalConjecturesUtil

/-!
# Erdős Problem 1037

*Reference:* [erdosproblems.com/1037](https://www.erdosproblems.com/1037)

Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice,
and the number of distinct degrees is $> (\frac{1}{2} + \varepsilon)n$. Must $G$
contain a trivial (empty or complete) subgraph of size 'much larger' than
$\log n$?

A question of Chen and Erdős [Er93, p.347]. The answer is no — Cambie, Chan,
and Hunter gave (in the comments section of the problem page) a simple
construction of a graph on $n$ vertices with at least $\frac{3}{4}n$ distinct
degrees, every degree appears at most twice, and the largest trivial subgraph
has size $O(\log n)$.

The problem is listed as DISPROVED (LEAN) on erdosproblems.com ("solved in the
negative and the proof verified in Lean"; page edition 22 September 2025,
accessed 2026-02-22). The page additionally thanks Stijn Cambie, Koishi Chan,
Zach Hunter, and Mehtaab Sawhney.

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
theory_. Quaestiones Mathematicae **16** (1993), 333–350.
-/

open SimpleGraph Finset

namespace Erdos1037

/--
**Erdős Problem 1037** (Disproved by Cambie, Chan, and Hunter) [Er93, p.347]:

Let $G$ be a graph on $n$ vertices in which every degree occurs at most twice,
and the number of distinct degrees is $> (1/2 + \varepsilon) \cdot n$. Must $G$
contain a trivial (empty or complete) subgraph of size much larger than
$\log n$?

The answer is no. Cambie, Chan, and Hunter gave a construction where the
largest trivial subgraph has size $O(\log n)$.
-/
@[category research solved, AMS 5]
theorem erdos_1037 :
    answer(False) ↔
    (∀ ε : ℝ, ε > 0 →
    ∀ C : ℝ, C > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
    ∀ _ : DecidableRel G.Adj,
      -- Every degree occurs at most twice
      (∀ d : ℕ, (Finset.univ.filter (fun v => G.degree v = d)).card ≤ 2) →
      -- The number of distinct degrees is > (1/2 + ε) · n
      ((Finset.univ.image (fun v => G.degree v)).card : ℝ) >
        (1 / 2 + ε) * (n : ℝ) →
      -- G contains a clique or independent set of size > C · log n
      (∃ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) ∧
        (S.card : ℝ) > C * Real.log n) ∨
      (∃ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) ∧
        (S.card : ℝ) > C * Real.log n)) := by
  sorry

/--
The Cambie–Chan–Hunter construction disproving Erdős Problem 1037:

There is a constant $C > 0$ such that for all sufficiently large $n$ there is a
graph $G$ on $n$ vertices with at least $\frac{3}{4}n$ distinct degrees, in
which every degree appears at most twice, and whose largest trivial (empty or
complete) subgraph has size at most $C \log n$.

Since $\frac{3}{4}n > (\frac{1}{2} + \varepsilon)n$ for every $\varepsilon <
\frac{1}{4}$, this witnesses the negation of the question in `erdos_1037`.
-/
@[category research solved, AMS 5]
theorem erdos_1037.variants.construction :
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ G : SimpleGraph (Fin n),
    ∃ _ : DecidableRel G.Adj,
      -- Every degree occurs at most twice
      (∀ d : ℕ, (Finset.univ.filter (fun v => G.degree v = d)).card ≤ 2) ∧
      -- The number of distinct degrees is at least (3/4) · n
      ((Finset.univ.image (fun v => G.degree v)).card : ℝ) ≥
        3 / 4 * (n : ℝ) ∧
      -- Every clique has size at most C · log n
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) ∧
      -- Every independent set has size at most C · log n
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ C * Real.log n) := by
  sorry

end Erdos1037
