import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #58

If G is a graph which contains odd cycles of ≤ k different lengths then
χ(G) ≤ 2k+2, with equality if and only if G contains K_{2k+2}.

Conjectured by Bollobás and Erdős. Bollobás and Shelah confirmed it for k=1.
Proved by Gyárfás [Gy92], who showed the stronger result that if G is 2-connected,
then G is either K_{2k+2} or contains a vertex of degree at most 2k.

Tags: graph theory, chromatic number, cycles
https://www.erdosproblems.com/58
-/

/-- The set of lengths of odd cycles in a graph G. -/
def oddCycleLengths {V : Type*} (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | Odd n ∧ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n}

/--
**Erdős Problem #58** (Bollobás–Erdős conjecture, proved by Gyárfás [Gy92]):

If G is a finite graph containing odd cycles of at most k different lengths,
then χ(G) ≤ 2k + 2, with equality if and only if G contains K_{2k+2} as a
clique subgraph.
-/
theorem erdos_problem_58 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : (oddCycleLengths G).ncard ≤ k) :
    G.chromaticNumber ≤ (2 * k + 2 : ℕ) ∧
    (G.chromaticNumber = (2 * k + 2 : ℕ) ↔ ∃ s : Finset V, G.IsNClique (2 * k + 2) s) :=
  sorry

end
