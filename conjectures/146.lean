import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

/-- An injective graph homomorphism from H to F; witnesses that F contains a
    subgraph isomorphic to H. -/
def containsSubgraph146 {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber146 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph146 F H ∧ F.edgeFinset.card = m}

/-- A graph G is r-degenerate if every non-empty finite set of vertices contains
    a vertex with at most r neighbors within that set. Equivalently, every induced
    subgraph of G has minimum degree at most r. -/
def IsRDegenerateGraph {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ (S : Set V), S.Finite → S.Nonempty →
    ∃ v ∈ S, (G.neighborSet v ∩ S).ncard ≤ r

/--
Erdős-Simonovits Conjecture (Problem #146) [ErSi84]:
If H is a bipartite graph that is r-degenerate (i.e., every induced subgraph of H
has minimum degree at most r), then

  ex(n; H) ≪ n^{2 - 1/r}

That is, there exists a constant C > 0 such that ex(n; H) ≤ C · n^{2 - 1/r} for all n ≥ 1.

This is open even for r = 2. Alon, Krivelevich, and Sudakov [AKS03] proved the
weaker bound ex(n; H) ≪ n^{2 - 1/(4r)}.
-/
theorem erdos_problem_146 :
    ∀ (r : ℕ), 1 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      IsRDegenerateGraph H r →
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
        (turanNumber146 H n : ℝ) ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ)) :=
  sorry
