import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #547

If T is a tree on n vertices then R(T) ≤ 2n - 2.

This was conjectured by Burr and Erdős [BuEr76]. It follows from the Erdős–Sós
conjecture [548], and has been proved for all large n by Zhao [Zh11].
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The diagonal Ramsey number R(G) for a graph G on Fin k: the minimum N such that
    every graph H on N vertices contains a copy of G or its complement contains
    a copy of G. -/
noncomputable def ramseyNumber {k : ℕ} (G : SimpleGraph (Fin k)) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G H ∨ ContainsSubgraphCopy G Hᶜ}

/--
Erdős Problem #547 [BuEr76]:

If T is a tree on n vertices then R(T) ≤ 2n - 2.
-/
theorem erdos_problem_547 (n : ℕ) (hn : n ≥ 2)
    (T : SimpleGraph (Fin n)) (hT : T.IsTree) :
    ramseyNumber T ≤ 2 * n - 2 :=
  sorry

end
