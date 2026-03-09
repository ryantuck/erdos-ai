import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

/--
A simple graph G on a finite vertex set is *sparse* if every induced subgraph
on k ≥ 2 vertices has at most 2k - 3 edges.
-/
def IsSparseGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, 2 ≤ S.card →
    (G.induce (↑S : Set V)).edgeFinset.card ≤ 2 * S.card - 3

/--
An embedding of G into F: an injective map on vertices that preserves adjacency.
-/
def IsGraphEmbedding {V W : Type*} (G : SimpleGraph V) (F : SimpleGraph W)
    (f : V ↪ W) : Prop :=
  ∀ u v, G.Adj u v → F.Adj (f u) (f v)

/--
A graph F has the size Ramsey property for (G, H) if every 2-coloring of
the edges of F yields either a monochromatic copy of G in color 0 or a
monochromatic copy of H in color 1.
-/
def HasSizeRamseyProp {V₁ V₂ W : Type*}
    (G : SimpleGraph V₁) (H : SimpleGraph V₂)
    (F : SimpleGraph W) [DecidableRel F.Adj] : Prop :=
  ∀ c : Sym2 W → Bool,
    (∃ f : V₁ ↪ W, ∀ u v, G.Adj u v →
      F.Adj (f u) (f v) ∧ c s(f u, f v) = true) ∨
    (∃ f : V₂ ↪ W, ∀ u v, H.Adj u v →
      F.Adj (f u) (f v) ∧ c s(f u, f v) = false)

/--
A graph has no isolated vertices: every vertex has at least one neighbor.
-/
def HasNoIsolatedVertices {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] : Prop :=
  ∀ v : V, 0 < H.degree v

/--
Erdős Problem #566 [EFRS93]:

Let G be such that any subgraph on k vertices has at most 2k - 3 edges.
Is it true that, if H has m edges and no isolated vertices, then R̂(G, H) ≪ m?

In other words, is G Ramsey size linear? This fails for a graph G with n vertices
and 2n - 2 edges (for example with H = Kₙ). Erdős, Faudree, Rousseau, and Schelp
have shown that any graph G with n vertices and at most n + 1 edges is Ramsey
size linear.

We state: for every sparse graph G, there exists a constant c > 0 such that for
every graph H with no isolated vertices and m edges, there exists a graph F with
at most c * m edges that has the size Ramsey property for (G, H).
-/
theorem erdos_problem_566 :
    ∀ (p : ℕ) (G : SimpleGraph (Fin p)) [DecidableRel G.Adj],
      IsSparseGraph G →
      ∃ c : ℕ, 0 < c ∧
        ∀ (n : ℕ) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
          HasNoIsolatedVertices H →
          ∃ (q : ℕ) (F : SimpleGraph (Fin q)) (_ : DecidableRel F.Adj),
            F.edgeFinset.card ≤ c * H.edgeFinset.card ∧
            HasSizeRamseyProp G H F :=
  sorry
