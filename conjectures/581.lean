import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph

/--
The maximum number of edges in a bipartite spanning subgraph of a graph G on
a finite vertex type. A spanning subgraph H ≤ G is bipartite iff it admits a
proper 2-coloring. We use `Set.ncard` to count edges, avoiding the need for
decidability instances.
-/
def maxBipartiteEdges {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ H : SimpleGraph V, H ≤ G ∧
    Nonempty (H.Coloring (Fin 2)) ∧
    H.edgeSet.ncard = k}

/--
f(m) is the largest k such that every triangle-free graph on m edges must
contain a bipartite subgraph with at least k edges. Equivalently, f(m) is
the infimum of `maxBipartiteEdges G` over all finite triangle-free graphs G
with exactly m edges. We quantify over graphs on `Fin n` for all n, which
suffices since every finite graph is isomorphic to one on `Fin n`.
-/
def erdos581_f (m : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 ∧
    G.edgeSet.ncard = m ∧
    maxBipartiteEdges G = k}

/--
Erdős Problem #581 [CEG79]:

Let f(m) be the maximal k such that a triangle-free graph on m edges must
contain a bipartite graph with k edges. Determine f(m).

Resolved by Alon [Al96], who showed that there exist constants c₁, c₂ > 0
such that m/2 + c₁·m^{4/5} ≤ f(m) ≤ m/2 + c₂·m^{4/5}.
-/
theorem erdos_problem_581 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ m : ℕ, 0 < m →
        (m : ℝ) / 2 + c₁ * (m : ℝ) ^ ((4 : ℝ) / 5) ≤ (erdos581_f m : ℝ) ∧
        (erdos581_f m : ℝ) ≤ (m : ℝ) / 2 + c₂ * (m : ℝ) ^ ((4 : ℝ) / 5) :=
  sorry

end
