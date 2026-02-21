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
def containsSubgraph147 {V U : Type*} (F : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → F.Adj (f u) (f v)

/-- The Turán number ex(n; H): the maximum number of edges in a simple graph on n
    vertices that contains no copy of H as a subgraph. -/
noncomputable def turanNumber147 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (fv : Fintype V) (F : SimpleGraph V) (dr : DecidableRel F.Adj),
    haveI := fv; haveI := dr;
    Fintype.card V = n ∧ ¬containsSubgraph147 F H ∧ F.edgeFinset.card = m}

/--
Erdős Problem #147 [ErSi84]:
If H is a bipartite graph with minimum degree r (i.e., every vertex of H has
degree at least r, where r ≥ 2), then there exists ε = ε(H) > 0 such that

  ex(n; H) ≫ n^{2 - 1/(r-1) + ε}

That is, there exist constants C > 0 and N₀ ∈ ℕ such that for all n ≥ N₀:
  ex(n; H) ≥ C · n^{2 - 1/(r-1) + ε}

This conjecture was DISPROVED: Janzer [Ja23] disproved it for even r ≥ 4, and
[Ja23b] disproved it for r = 3, constructing for any δ > 0 a 3-regular bipartite
graph H with ex(n; H) ≪ n^{4/3 + δ}.
-/
theorem erdos_problem_147 :
    ∀ (r : ℕ), 2 ≤ r →
    ∀ (U : Type*) (H : SimpleGraph U) [Fintype U] [DecidableRel H.Adj],
      Nonempty (H.Coloring (Fin 2)) →
      (∀ v : U, r ≤ H.degree v) →
      ∃ ε : ℝ, 0 < ε ∧
        ∃ C : ℝ, 0 < C ∧
          ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
            C * (n : ℝ) ^ ((2 : ℝ) - 1 / ((r : ℝ) - 1) + ε) ≤ (turanNumber147 H n : ℝ) :=
  sorry
