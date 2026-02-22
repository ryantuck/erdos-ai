import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Basic

open SimpleGraph Cardinal

noncomputable section

/-!
# Erdős Problem #638

Let $S$ be a family of finite graphs such that for every $n$ there is some
$G_n \in S$ such that if the edges of $G_n$ are coloured with $n$ colours
then there is a monochromatic triangle.

Is it true that for every infinite cardinal $\aleph$ there is a graph $G$ of
which every finite subgraph is in $S$ and if the edges of $G$ are coloured
with $\aleph$ many colours then there is a monochromatic triangle.
-/

/-- A symmetric colouring of a simple graph has a **monochromatic triangle**
    if three pairwise-adjacent vertices have all three edges the same colour. -/
def HasMonoTriangle {V : Type*} (G : SimpleGraph V) {α : Type*}
    (c : V → V → α) : Prop :=
  ∃ a b d : V, G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
    c a b = c b d ∧ c a b = c a d

/-- The induced subgraph of G pulled back along an embedding f : Fin m ↪ V. -/
def inducedFinSubgraph {V : Type*} (G : SimpleGraph V) {m : ℕ}
    (f : Fin m ↪ V) : SimpleGraph (Fin m) where
  Adj i j := G.Adj (f i) (f j)
  symm _ _ h := G.symm h
  loopless := ⟨fun i h => G.loopless.1 (f i) h⟩

/-- Two graphs on Fin m are isomorphic via a permutation of vertices. -/
def FinGraphIso {m : ℕ} (G H : SimpleGraph (Fin m)) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), ∀ i j, G.Adj i j ↔ H.Adj (σ i) (σ j)

/--
**Erdős Problem #638**

Let S be a family of finite graphs (indexed by vertex count) with the Ramsey
property: for every n ≥ 1, some member of S forces a monochromatic triangle
under any n-colouring of its edges.

Conjecture: for every infinite cardinal κ, there exists a graph G such that
every finite induced subgraph of G belongs (up to isomorphism) to S, and
every κ-colouring of the edges of G contains a monochromatic triangle.
-/
theorem erdos_problem_638
    (S : (m : ℕ) → Set (SimpleGraph (Fin m)))
    (hS : ∀ n : ℕ, n ≥ 1 →
      ∃ m : ℕ, ∃ G ∈ S m,
        ∀ (c : Fin m → Fin m → Fin n), (∀ u v, c u v = c v u) →
          HasMonoTriangle G c)
    (κ : Cardinal) (hκ : ℵ₀ ≤ κ) :
    ∃ (V : Type) (G : SimpleGraph V),
      (∀ (m : ℕ) (f : Fin m ↪ V),
        ∃ H ∈ S m, FinGraphIso (inducedFinSubgraph G f) H) ∧
      ∀ (α : Type) (_ : #α = κ) (c : V → V → α),
        (∀ u v, c u v = c v u) → HasMonoTriangle G c :=
  sorry

end
