import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic

open SimpleGraph

/--
Erdős Problem #71 (Erdős-Burr conjecture, proved by Bollobás [Bo77]):
For every infinite arithmetic progression P = {a, a+d, a+2d, …} (with d ≥ 1)
that contains even numbers, there exists a constant c = c(P) > 0 such that every
finite graph with average degree at least c contains a cycle whose length belongs to P.

The average degree of a graph G on n > 0 vertices is 2|E(G)|/n.
-/
theorem erdos_problem_71 (a d : ℕ) (hd : 1 ≤ d) (heven : ∃ k : ℕ, Even (a + k * d)) :
    ∃ c : ℝ, c > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        0 < Fintype.card V →
        c ≤ (2 * (G.edgeFinset.card : ℝ)) / (Fintype.card V : ℝ) →
        ∃ m : ℕ, (∃ k : ℕ, m = a + k * d) ∧
          ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m :=
  sorry
