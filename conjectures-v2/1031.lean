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
# Erdős Problem 1031

*Reference:* [erdosproblems.com/1031](https://www.erdosproblems.com/1031)

A question of Erdős, Fajtlowicz, and Staton [Er93, p.340]: if $G$ is a graph on $n$
vertices which contains no trivial (empty or complete) subgraph on $\geq 10\log n$ many
vertices, then must $G$ contain an induced non-trivial regular subgraph on $\gg \log n$
many vertices?

Erdős [Er93] writes: "Perhaps very much more is true but we could not even prove this
seemingly weak result".

By Ramsey's theorem every graph on $n$ vertices contains a trivial subgraph on
$\gg \log n$ many vertices, so the hypothesis is a natural "barely non-Ramsey" regime.

The answer is yes (status on the problem page: PROVED). This was proved by Prömel and
Rödl [PrRo99], in the strong sense that, for any $c > 0$, if $G$ contains no trivial
subgraph on $\geq c\log n$ vertices then $G$ contains all graphs with $O_c(\log n)$ many
vertices as induced subgraphs.

See also Erdős Problem [82] for how large an induced regular subgraph a general graph
must contain.

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[PrRo99] Prömel, H.J. and Rödl, V., _Non-Ramsey graphs are c log n-universal_.
J. Combin. Theory Ser. A (1999), 379–384.
-/

open scoped Topology Real

namespace Erdos1031

/--
**Erdős Problem 1031** [Er93, p.340]:

If $G$ is a graph on $n$ vertices with no clique and no independent set of size
$\geq 10 \log n$, must $G$ contain an induced regular subgraph on $\geq c \log n$
vertices (for some absolute constant $c > 0$) that is neither empty nor complete?

A "trivial" subgraph means an empty or complete induced subgraph (i.e. an independent
set or a clique). Regularity of the induced subgraph on $S$ means every vertex of $S$
has the same number $d$ of neighbours within $S$; it is non-trivial iff
$1 \le d \le |S| - 2$.

The answer is yes: this was proved by Prömel and Rödl [PrRo99], who showed the stronger
result that for any $c > 0$, if $G$ contains no trivial subgraph on $\geq c \log n$
vertices then $G$ contains all graphs with $O_c(\log n)$ vertices as induced subgraphs.
-/
@[category research solved, AMS 5]
theorem erdos_1031 : answer(True) ↔
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n), ∀ _ : DecidableRel G.Adj,
      G.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      Gᶜ.CliqueFree ⌈10 * Real.log (↑n)⌉₊ →
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ c * Real.log (↑n) ∧
        ∃ d : ℕ, d ≥ 1 ∧ d + 1 < S.card ∧
          ∀ v ∈ S, (S.filter (G.Adj v)).card = d := by
  sorry

/--
By Ramsey's theorem, every graph on $n$ vertices contains a trivial (empty or complete)
induced subgraph on $\gg \log n$ many vertices. This classical fact, recorded on the
problem page, is what makes the hypothesis of Erdős Problem 1031 a "barely non-Ramsey"
regime: the constant $10$ there cannot be replaced by an arbitrarily small one.
-/
@[category research solved, AMS 5]
theorem erdos_1031.variants.ramsey :
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      ∃ S : Finset (Fin n),
        (S.card : ℝ) ≥ c * Real.log (↑n) ∧
        ((∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨ (∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)) := by
  sorry

/--
The strong form proved by Prömel and Rödl [PrRo99]: for any $c > 0$ there is a constant
$C > 0$ (depending on $c$) such that, for all sufficiently large $n$, if $G$ is a graph
on $n$ vertices containing no trivial (empty or complete) subgraph on $\geq c \log n$
many vertices, then $G$ contains **every** graph on at most $C \log n$ vertices as an
induced subgraph. Applied to a non-trivial regular graph on $\sim C \log n$ vertices,
this answers Erdős Problem 1031 affirmatively.
-/
@[category research solved, AMS 5]
theorem erdos_1031.variants.promel_rodl_universal :
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      G.CliqueFree ⌈c * Real.log (↑n)⌉₊ →
      Gᶜ.CliqueFree ⌈c * Real.log (↑n)⌉₊ →
      ∀ m : ℕ, (m : ℝ) ≤ C * Real.log (↑n) →
      ∀ H : SimpleGraph (Fin m),
        ∃ f : Fin m → Fin n, Function.Injective f ∧
          ∀ i j : Fin m, H.Adj i j ↔ G.Adj (f i) (f j) := by
  sorry

end Erdos1031
