import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #585

What is the maximum number of edges that a graph on n vertices can have if it
does not contain two edge-disjoint cycles with the same vertex set?

A problem of Erdős [Er76b].

Pyber, Rödl, and Szemerédi [PRS95] constructed such a graph with ≫ n log log n
edges (lower bound).

Chakraborti, Janzer, Methuku, and Montgomery [CJMM24] showed that such a
graph can have at most n · (log n)^{O(1)} many edges (upper bound).
-/

/-- A graph has no two edge-disjoint cycles with the same vertex set. -/
def NoTwoEdgeDisjointCyclesSameVertexSet {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ¬∃ (u v : Fin n) (c₁ : G.Walk u u) (c₂ : G.Walk v v),
    c₁.IsCycle ∧ c₂.IsCycle ∧
    c₁.support.toFinset = c₂.support.toFinset ∧
    Disjoint c₁.edges.toFinset c₂.edges.toFinset

/-- The maximum number of edges in a graph on n vertices with no two
    edge-disjoint cycles sharing the same vertex set. -/
noncomputable def maxEdgesNoEdgeDisjointCycles (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    NoTwoEdgeDisjointCyclesSameVertexSet G ∧ G.edgeFinset.card = m}

/--
Erdős Problem #585, Lower Bound [PRS95]:

There exists a constant c > 0 such that for all sufficiently large n,
the maximum number of edges in an n-vertex graph with no two edge-disjoint
cycles on the same vertex set is at least c · n · log(log(n)).
-/
theorem erdos_problem_585_lower_bound :
    ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) * Real.log (Real.log (n : ℝ)) ≤
        (maxEdgesNoEdgeDisjointCycles n : ℝ) :=
  sorry

/--
Erdős Problem #585, Upper Bound [CJMM24]:

There exists a constant C > 0 such that for all sufficiently large n,
the maximum number of edges in an n-vertex graph with no two edge-disjoint
cycles on the same vertex set is at most n · (log n)^C.
-/
theorem erdos_problem_585_upper_bound :
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (maxEdgesNoEdgeDisjointCycles n : ℝ) ≤
        (n : ℝ) * (Real.log (n : ℝ)) ^ C :=
  sorry

end
