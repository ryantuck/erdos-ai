import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #79

We say G is *Ramsey size linear* if R(G,H) ≪ m for all graphs H with m edges
and no isolated vertices.

Are there infinitely many graphs G which are not Ramsey size linear but such
that all of its proper subgraphs are?

Asked by Erdős, Faudree, Rousseau, and Schelp [EFRS93].
Proved by Wigderson [Wi24]. K₄ is the only explicitly known example.
-/

/-- `IsSubgraphOf H G` means H is isomorphic to a subgraph of G: there exists an
    injection from V(H) to V(G) that preserves adjacency. -/
def IsSubgraphOf {α β : Type*} (H : SimpleGraph α) (G : SimpleGraph β) : Prop :=
  ∃ f : α → β, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- The Ramsey property: every 2-coloring of K_n contains G in one color or H in the
    other. A 2-coloring of K_n is a graph S on Fin n; one color class is S and the
    other is Sᶜ (the complement). -/
def RamseyProp {p q : ℕ} (G : SimpleGraph (Fin p)) (H : SimpleGraph (Fin q))
    (n : ℕ) : Prop :=
  ∀ S : SimpleGraph (Fin n), IsSubgraphOf G S ∨ IsSubgraphOf H Sᶜ

/-- A graph has no isolated vertices if every vertex has at least one neighbor. -/
def NoIsolatedVertices {q : ℕ} (H : SimpleGraph (Fin q)) : Prop :=
  ∀ v : Fin q, ∃ w : Fin q, H.Adj v w

/-- A graph G is Ramsey size linear if there exists C > 0 such that for every graph H
    with no isolated vertices, the Ramsey property R(G,H) holds at some n ≤ C · |E(H)|. -/
def IsRamseySizeLinear {p : ℕ} (G : SimpleGraph (Fin p)) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (q : ℕ) (H : SimpleGraph (Fin q)) [DecidableRel H.Adj],
    NoIsolatedVertices H →
    ∃ n : ℕ, (n : ℝ) ≤ C * (H.edgeFinset.card : ℝ) ∧ RamseyProp G H n

/-- **Erdős Problem #79**: There exist infinitely many graphs which are not Ramsey
    size linear but all of whose proper subgraphs are. A graph H is a proper subgraph
    of G if H embeds into G (as a subgraph) but G does not embed into H. -/
theorem erdos_conjecture_79 :
    ∀ N : ℕ, ∃ (p : ℕ) (G : SimpleGraph (Fin p)),
      p ≥ N ∧
      ¬ IsRamseySizeLinear G ∧
      ∀ (q : ℕ) (H : SimpleGraph (Fin q)),
        IsSubgraphOf H G →
        ¬ IsSubgraphOf G H →
        IsRamseySizeLinear H := by
  sorry
