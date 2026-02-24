import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #22 (Bollobás–Erdős Ramsey–Turán Conjecture)

Let ε > 0 and n be sufficiently large depending on ε. Is there a graph on n
vertices with ≥ n²/8 many edges which contains no K₄ such that the largest
independent set has size at most εn?

Equivalently: rt(n; 4, εn) ≥ n²/8 for sufficiently large n, where rt(n; k, ℓ)
is the Ramsey–Turán number.

Conjectured by Bollobás and Erdős [BoEr76], who proved the existence of such
a graph with (1/8 + o(1))n² many edges. Proved by Fox, Loh, and Zhao [FLZ15],
who showed that for every n ≥ 1 there exists a K₄-free graph on n vertices
with ≥ n²/8 edges and independence number ≪ (log log n)^{3/2} / (log n)^{1/2} · n.

Tags: graph theory
https://www.erdosproblems.com/22
-/

/--
**Erdős Problem #22** (Bollobás–Erdős Conjecture on Ramsey–Turán numbers,
proved by Fox, Loh, and Zhao [FLZ15]):

For every ε > 0, for all sufficiently large n, there exists a graph G on n
vertices such that:
- G has at least n²/8 edges,
- G contains no K₄ (no clique of size 4),
- every independent set in G has size at most ε·n.
-/
theorem erdos_problem_22 :
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        ∃ G : SimpleGraph (Fin n),
          (n : ℝ) ^ 2 / 8 ≤ (G.edgeSet.ncard : ℝ) ∧
          (∀ s : Finset (Fin n), ¬G.IsNClique 4 s) ∧
          (∀ s : Finset (Fin n), G.IsIndepSet ↑s → (s.card : ℝ) ≤ ε * (n : ℝ)) :=
  sorry
