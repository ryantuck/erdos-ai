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
# Erdős Problem 1091

*Reference:* [erdosproblems.com/1091](https://www.erdosproblems.com/1091)

Let $G$ be a $K_4$-free graph with chromatic number $4$. Must $G$ contain an odd cycle
with at least two diagonals?

More generally, is there some $f(r) \to \infty$ such that every graph with chromatic
number $4$, in which every subgraph on $\leq r$ vertices has chromatic number $\leq 3$,
contains an odd cycle with at least $f(r)$ diagonals?

Erdős originally asked about the existence of just one diagonal, which is true, and was
proved by Larson [La79]. In fact Larson proved the following stronger conjecture of
Bollobás and Erdős: if $G$ is a $K_4$-free graph containing no odd cycle with a diagonal
then either $G$ is bipartite, or $G$ contains a cut vertex, or $G$ contains a vertex with
degree $\leq 2$.

The pentagonal wheel shows that three diagonals are not guaranteed.

The first question was solved in the affirmative by Voss [Vo82]. The general $f(r)$
question remains open; the problem page's overall status is OPEN (page last edited
06 December 2025, accessed 2026-02-23).

[Er76c] Erdős, P., *Problems in combinatorics and graph theory* (1976).

[La79] Larson — proved that $K_4$-free graphs with chromatic number $4$ contain an odd cycle
with at least one diagonal. (Bibliographic details not recoverable from the archived page.)

[Vo82] Voss — strengthened Larson's result to at least two diagonals. (Bibliographic details
not recoverable from the archived page.)
-/

open SimpleGraph Classical Filter

namespace Erdos1091

/-- A graph $G$ contains an odd cycle with at least $d$ diagonals.

An odd cycle of length $2m+3$ ($\geq 3$) is given by an injective map $f : \text{Fin}(2m+3) \to V$
where consecutive vertices (cyclically) are adjacent in $G$. A diagonal is an edge
of $G$ between two cycle vertices that are not consecutive in the cycle. -/
noncomputable def HasOddCycleWithDiagonals {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (f : Fin (2 * m + 3) → V),
    Function.Injective f ∧
    (∀ i : Fin (2 * m + 3),
      G.Adj (f i) (f ⟨(i.val + 1) % (2 * m + 3), Nat.mod_lt _ (by omega)⟩)) ∧
    d ≤ (Finset.univ.filter (fun p : Fin (2 * m + 3) × Fin (2 * m + 3) =>
      p.1.val < p.2.val ∧
      G.Adj (f p.1) (f p.2) ∧
      p.2.val ≠ (p.1.val + 1) % (2 * m + 3) ∧
      p.1.val ≠ (p.2.val + 1) % (2 * m + 3))).card

/--
Erdős Problem 1091, first question [Er76c, p.4]:

Let $G$ be a $K_4$-free graph with chromatic number $4$. Must $G$ contain an odd cycle
with at least two diagonals?

Solved in the affirmative by Voss [Vo82], so the answer is `True`. Erdős originally
asked about one diagonal, proved by Larson [La79]. The pentagonal wheel shows that
three diagonals cannot be guaranteed.
-/
@[category research solved, AMS 5]
theorem erdos_1091 :
    answer(True) ↔
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 → G.chromaticNumber = (4 : ℕ∞) →
      HasOddCycleWithDiagonals G 2 := by
  sorry

/--
Erdős Problem 1091, second question (open) [Er76c, p.4]:

More generally, is there a function $f : \mathbb{N} \to \mathbb{N}$ with $f(r) \to \infty$
such that every graph $G$ with chromatic number $4$, in which every subgraph on $\leq r$
vertices has chromatic number $\leq 3$, contains an odd cycle with at least $f(r)$ diagonals?

The source's "every subgraph on $\leq r$ vertices" is formalized via induced subgraphs on
vertex sets of size $\leq r$; the two readings are equivalent, since the chromatic number
of a subgraph is at most that of the induced subgraph on the same vertex set.
-/
@[category research open, AMS 5]
theorem erdos_1091.variants.unbounded_diagonals :
    answer(sorry) ↔
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧
      ∀ (r n : ℕ) (G : SimpleGraph (Fin n)),
        G.chromaticNumber = (4 : ℕ∞) →
        (∀ S : Finset (Fin n), S.card ≤ r →
          (G.induce (↑S : Set (Fin n))).chromaticNumber ≤ (3 : ℕ∞)) →
        HasOddCycleWithDiagonals G (f r) := by
  sorry

/--
Erdős Problem 1091, variant (proved by Larson [La79]):

Every $K_4$-free graph with chromatic number $4$ contains an odd cycle with at least one
diagonal. This was Erdős's original question, answered affirmatively by Larson and
subsumed by Voss's two-diagonal theorem [Vo82].
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.one_diagonal (n : ℕ) (G : SimpleGraph (Fin n))
    (hK4 : G.CliqueFree 4) (hχ : G.chromaticNumber = (4 : ℕ∞)) :
    HasOddCycleWithDiagonals G 1 := by
  sorry

/--
Erdős Problem 1091, variant (sharpness):

Three diagonals are not guaranteed: there is a $K_4$-free graph with chromatic number $4$
containing no odd cycle with three or more diagonals. The pentagonal wheel ($C_5$ plus a
dominating hub, on $6$ vertices) is such a graph: its odd cycles are triangles, $C_5$
itself, and $5$-cycles through the hub, and none of these has more than two diagonals.
-/
@[category research solved, AMS 5]
theorem erdos_1091.variants.three_diagonals_not_guaranteed :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      G.CliqueFree 4 ∧ G.chromaticNumber = (4 : ℕ∞) ∧
      ¬ HasOddCycleWithDiagonals G 3 := by
  sorry

end Erdos1091
