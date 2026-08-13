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
# Erdős Problem 1036

*Reference:* [erdosproblems.com/1036](https://www.erdosproblems.com/1036)

Let $G$ be a graph on $n$ vertices which does not contain a trivial (empty or complete)
graph on more than $c\log n$ vertices. Must $G$ contain at least $2^{\Omega_c(n)}$ many
induced subgraphs which are not pairwise isomorphic?

A question of Erdős and Rényi [Er93, p.346] [Va99, 3.53]. This is true, and was proved by
Shelah [Sh98]. The problem page (edition of 23 January 2026, accessed 2026-02-22) marks the
status PROVED (LEAN): "This has been solved in the affirmative and the proof verified in
Lean."

Alon and Hajnal [AlHa91] proved that $G$ must contain at least
$\exp\left(n(\log n)^{-O(\log\log n)}\right)$ many non-isomorphic induced subgraphs.

Erdős and Hajnal [ErHa89b] proved that if $G$ does not contain a complete bipartite graph
or its complement on more than $c\log n$ vertices then $G$ contains at least
$2^{\Omega_c(n)}$ many non-isomorphic induced subgraphs.

[Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph theory_.
Quaestiones Mathematicae **16** (1993), 333–350.

[Va99] Various, _Some of Paul's favorite problems_. Booklet produced for the conference
"Paul Erdős and his mathematics", Budapest, July 1999 (1999), §3.53.

[Sh98] Shelah, S., _Erdős and Rényi conjecture_. J. Combin. Theory Ser. A 82 (1998), no. 2,
179–185.

[AlHa91] Alon, N. and Hajnal, A., _Ramsey graphs contain many distinct induced subgraphs_.
Graphs Combin. (1991), 1–6.

[ErHa89b] Erdős, P. and Hajnal, A., _On the number of distinct induced subgraphs of a graph_.
Discrete Math. (1989), 145–154.
-/

open SimpleGraph Finset

namespace Erdos1036

/--
**Erdős Problem 1036** (Proved by Shelah [Sh98]) [Er93, p.346] [Va99, 3.53]:

Let $G$ be a graph on $n$ vertices which does not contain a trivial (empty or complete)
graph on more than $c\log n$ vertices. Must $G$ contain at least $2^{\Omega_c(n)}$ many
induced subgraphs which are not pairwise isomorphic?

The answer is yes: for every $c > 0$, there exist $\delta > 0$ and $N_0$ such that for all
$n \geq N_0$, if $G$ is a graph on $n$ vertices with no clique and no independent set of
size greater than $c \cdot \log n$, then $G$ has at least $2^{\delta n}$ pairwise
non-isomorphic induced subgraphs.

Here "trivial graph" means empty (independent set) or complete (clique), and
$\log$ denotes the natural logarithm (the choice of base is absorbed by $c$).
-/
@[category research solved, AMS 5]
theorem erdos_1036 :
    answer(True) ↔
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      ∃ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≥ (2 : ℝ) ^ (δ * (n : ℝ)) ∧
        ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
          ¬Nonempty (G.induce (↑S : Set (Fin n)) ≃g G.induce (↑T : Set (Fin n))) := by
  sorry

/--
**Alon–Hajnal lower bound** (Proved) [AlHa91]:

Under the same hypotheses as `erdos_1036` — no clique and no independent set on more than
$c \log n$ vertices — $G$ must contain at least
$\exp\left(n(\log n)^{-O(\log\log n)}\right)$ many pairwise non-isomorphic induced
subgraphs. This was the strongest known lower bound before Shelah's proof.

The asymptotic is unpacked as: there is a constant $C > 0$ (depending on $c$) such that
for all sufficiently large $n$ the count is at least
$\exp\big(n \cdot (\log n)^{-C \log\log n}\big)$.
-/
@[category research solved, AMS 5]
theorem erdos_1036.variants.alon_hajnal :
    ∀ c : ℝ, c > 0 →
    ∃ C : ℝ, C > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      (∀ S : Finset (Fin n), G.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      (∀ S : Finset (Fin n), Gᶜ.IsClique (↑S : Set (Fin n)) →
        (S.card : ℝ) ≤ c * Real.log n) →
      ∃ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≥
          Real.exp ((n : ℝ) * (Real.log n) ^ (-(C * Real.log (Real.log n)))) ∧
        ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
          ¬Nonempty (G.induce (↑S : Set (Fin n)) ≃g G.induce (↑T : Set (Fin n))) := by
  sorry

/--
**Erdős–Hajnal bipartite strengthening** (Proved) [ErHa89b]:

If $G$ does not contain a complete bipartite graph or its complement on more than
$c \log n$ vertices, then $G$ contains at least $2^{\Omega_c(n)}$ many pairwise
non-isomorphic induced subgraphs.

Here "$G$ contains a complete bipartite graph on a vertex set" is read in the induced
sense: disjoint parts $A$, $B$ with every edge between $A$ and $B$ present and no edges
inside $A$ or inside $B$; the complement case swaps edges and non-edges. Taking
$A = \emptyset$ recovers independent sets (resp. cliques), so this hypothesis is stronger
than that of `erdos_1036`, of which this result was a partial precursor. (The non-induced
reading would make the hypothesis unsatisfiable for large $n$: any vertex together with
its neighbourhood or non-neighbourhood would already give a forbidden configuration.)
-/
@[category research solved, AMS 5]
theorem erdos_1036.variants.erdos_hajnal_bipartite :
    ∀ c : ℝ, c > 0 →
    ∃ δ : ℝ, δ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ G : SimpleGraph (Fin n),
      (∀ A B : Finset (Fin n), Disjoint A B →
        Gᶜ.IsClique (↑A : Set (Fin n)) → Gᶜ.IsClique (↑B : Set (Fin n)) →
        (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) →
        ((A ∪ B).card : ℝ) ≤ c * Real.log n) →
      (∀ A B : Finset (Fin n), Disjoint A B →
        G.IsClique (↑A : Set (Fin n)) → G.IsClique (↑B : Set (Fin n)) →
        (∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) →
        ((A ∪ B).card : ℝ) ≤ c * Real.log n) →
      ∃ F : Finset (Finset (Fin n)),
        (F.card : ℝ) ≥ (2 : ℝ) ^ (δ * (n : ℝ)) ∧
        ∀ S ∈ F, ∀ T ∈ F, S ≠ T →
          ¬Nonempty (G.induce (↑S : Set (Fin n)) ≃g G.induce (↑T : Set (Fin n))) := by
  sorry

end Erdos1036
