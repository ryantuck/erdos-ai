import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #714

Is it true that ex(n; K_{r,r}) ≫ n^{2-1/r} for all r ≥ 2?

Here K_{r,r} is the complete bipartite graph with both parts of size r, and
ex(n; H) is the Turán extremal number: the maximum number of edges in a simple
graph on n vertices containing no copy of H as a subgraph.

The notation ≫ means there exists a constant C > 0 such that
ex(n; K_{r,r}) ≥ C · n^{2-1/r} for all sufficiently large n.

Kövári, Sós, and Turán proved the matching upper bound
ex(n; K_{r,r}) ≪ n^{2-1/r} for all r ≥ 2. The conjecture asks whether
the lower bound of the same order also holds.

The conjectured lower bound is known for r = 2 and r = 3.
-/

/-- A graph G contains H as a subgraph via an injective graph homomorphism. -/
def ContainsSubgraph714 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- The Turán extremal number ex(n; H): the maximum number of edges in a
    simple graph on n vertices that does not contain H as a subgraph. -/
noncomputable def extremalNumber714 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph714 G H ∧ G.edgeSet.ncard = m}

/--
Erdős Problem #714:

For every r ≥ 2, the extremal number ex(n; K_{r,r}) satisfies a lower bound
of order n^{2-1/r}. That is, there exist C > 0 and N₀ such that for all
n ≥ N₀:
  ex(n; K_{r,r}) ≥ C · n^{2-1/r}.

Here K_{r,r} is represented by `completeBipartiteGraph (Fin r) (Fin r)` from
Mathlib, the complete bipartite graph on `Fin r ⊕ Fin r`.
-/
theorem erdos_problem_714 :
    ∀ r : ℕ, 2 ≤ r →
      ∃ C : ℝ, 0 < C ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) ≤
            (extremalNumber714 (completeBipartiteGraph (Fin r) (Fin r)) n : ℝ) :=
  sorry

end
