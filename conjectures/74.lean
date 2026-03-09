import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Data.Finset.Prod

open Filter SimpleGraph Finset

/--
Erdős Problem #74 [EHS82][Er87][Er90][Er93,p.342][Er94b][Er95][Er95d,p.62][Er96][Er97b][Er97c][Er97d][Er97f]:

Let f(n) → ∞ (possibly very slowly). Is there a graph of infinite chromatic
number such that every finite subgraph on n vertices can be made bipartite by
deleting at most f(n) edges?

Conjectured by Erdős, Hajnal, and Szemerédi. Rödl proved this for hypergraphs
and also proved there is such a graph (with chromatic number ℵ₀) if f(n) = εn
for any fixed ε > 0. It is open even for f(n) = √n.

The formalization states: for any f : ℕ → ℕ tending to infinity, there exists
a graph G with infinite chromatic number such that for every finite subset S
of vertices, there is a 2-coloring with at most f(|S|) monochromatic edges.
The count uses ordered pairs (each unordered edge counted twice), hence the
factor of 2.
-/
theorem erdos_problem_74 :
    ∀ f : ℕ → ℕ, Tendsto f atTop atTop →
      ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        (∀ k : ℕ, ¬G.Colorable k) ∧
        ∀ (S : Finset V),
          ∃ c : V → Bool,
            ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2 ∧ c p.1 = c p.2)).card
              ≤ 2 * f S.card :=
  sorry
