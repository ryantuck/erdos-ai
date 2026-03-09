import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Subgraph

open SimpleGraph

/-!
# Erdős Problem #108

For every r ≥ 4 and k ≥ 2 is there some finite f(k,r) such that every graph
of chromatic number ≥ f(k,r) contains a subgraph of girth ≥ r and chromatic
number ≥ k?

Conjectured by Erdős and Hajnal. Rödl [Ro77] proved the r = 4 case.

Tags: graph theory, chromatic number, cycles
-/

/--
**Erdős Problem #108** [Er71, Er79b, Er81, Er90, Er95d]:

For every r ≥ 4 and k ≥ 2 there exists a finite f(k,r) such that every graph
of chromatic number ≥ f(k,r) contains a subgraph of girth ≥ r and chromatic
number ≥ k.
-/
theorem erdos_problem_108 (r : ℕ) (hr : r ≥ 4) (k : ℕ) (hk : k ≥ 2) :
    ∃ f : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      f ≤ G.chromaticNumber →
      ∃ (G' : G.Subgraph),
        r ≤ G'.coe.girth ∧ k ≤ G'.coe.chromaticNumber :=
  sorry
