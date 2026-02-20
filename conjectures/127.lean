import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot

open Real Filter

/--
For a finite simple graph G and a vertex subset S, the cut defined by S
consists of edges with exactly one endpoint in S. We count these as ordered pairs
(v, w) with v ∈ S, w ∉ S, and G.Adj v w; since G.Adj is symmetric and S and Sᶜ
are disjoint, each undirected cut edge is counted exactly once (from its S-side endpoint).
-/
noncomputable def cutSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : V × V =>
    p.1 ∈ S ∧ p.2 ∉ S ∧ G.Adj p.1 p.2).card

/--
The maximum bipartite subgraph size of G: the maximum over all vertex bipartitions
(S, Sᶜ) of the number of edges crossing the cut. This equals the maximum number of
edges in any bipartite subgraph of G (the max-cut).
-/
noncomputable def maxBipartiteSubgraphSize {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (cutSize G)

/--
The Edwards lower bound: every graph with m edges has a bipartite subgraph of size at
least m/2 + (√(8m+1) − 1)/8. Proved by Edwards [Ed73].
-/
noncomputable def edwardsLB (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

/--
f(m) is the maximal value r such that every finite simple graph with m edges has a
bipartite subgraph with at least edwardsLB(m) + r edges. Equivalently, f(m) is the
infimum over all finite simple graphs G with exactly m edges of the excess
  maxBipartiteSubgraphSize(G) − edwardsLB(m).

Edwards [Ed73] proved f(m) ≥ 0 for all m. Note that f(C(n,2)) = 0, achieved by Kₙ.
-/
noncomputable def f (m : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    G.edgeFinset.card = m ∧ r = (maxBipartiteSubgraphSize G : ℝ) - edwardsLB m}

/--
Erdős Problem #127 (Erdős–Kohayakawa–Gyárfás; solved by Alon [Al96]):
Let f(m) be maximal such that every graph with m edges contains a bipartite subgraph with
at least m/2 + (√(8m+1) − 1)/8 + f(m) edges.
There exists an infinite sequence of integers (mᵢ) with mᵢ → ∞ such that f(mᵢ) → ∞.

Edwards [Ed73] proved f(m) ≥ 0 for all m.
Alon [Al96] proved this in the affirmative: f(n²/2) ≫ n^(1/2).
Alon [Al96] also showed the upper bound f(m) ≪ m^(1/4) for all m.
-/
theorem erdos_problem_127 :
    ∃ (seq : ℕ → ℕ), StrictMono seq ∧
      Filter.Tendsto (fun i => f (seq i)) Filter.atTop Filter.atTop :=
  sorry
