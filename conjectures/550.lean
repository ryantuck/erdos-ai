import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #550

Let m₁ ≤ ⋯ ≤ mₖ and n be sufficiently large. If T is a tree on n vertices
and G is the complete multipartite graph with vertex class sizes m₁, …, mₖ,
then R(T, G) ≤ (χ(G) - 1)(R(T, K_{m₁,m₂}) - 1) + m₁.

For a complete k-partite graph with k ≥ 2 non-empty parts, χ(G) = k, so the
bound becomes (k - 1)(R(T, K_{m₁,m₂}) - 1) + m₁.

Chvátal [Ch77] proved that R(T, Kₘ) = (m - 1)(n - 1) + 1.
-/

/-- A graph H contains a copy of graph G (as a subgraph) if there is an injective
    function from V(G) to V(H) that preserves adjacency. -/
def ContainsSubgraphCopy {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The off-diagonal Ramsey number R(G₁, G₂): the minimum N such that every
    graph H on N vertices contains a copy of G₁ or its complement contains a
    copy of G₂. -/
noncomputable def offDiagRamseyNumber {V₁ V₂ : Type*}
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) : ℕ :=
  sInf {N : ℕ | ∀ (H : SimpleGraph (Fin N)),
    ContainsSubgraphCopy G₁ H ∨ ContainsSubgraphCopy G₂ Hᶜ}

/-- The complete multipartite graph with vertex class sizes given by `sizes`.
    Vertices are pairs (i, j) where i indexes the part and j is within the part.
    Two vertices are adjacent iff they belong to different parts. -/
def completeMultipartiteGraph {k : ℕ} (sizes : Fin k → ℕ) :
    SimpleGraph (Σ i : Fin k, Fin (sizes i)) where
  Adj v w := v.1 ≠ w.1
  symm _ _ h := Ne.symm h
  loopless := ⟨fun _ h => h rfl⟩

/-- Part sizes for the complete bipartite graph K_{m₁,m₂}. -/
def bipSizes (m₁ m₂ : ℕ) : Fin 2 → ℕ
  | ⟨0, _⟩ => m₁
  | ⟨_ + 1, _⟩ => m₂

/--
Erdős Problem #550 [EFRS85]:

Let m₁ ≤ ⋯ ≤ mₖ and n be sufficiently large. If T is a tree on n vertices and
G is the complete multipartite graph with vertex class sizes m₁, …, mₖ, then
  R(T, G) ≤ (χ(G) - 1)(R(T, K_{m₁,m₂}) - 1) + m₁.

For a complete k-partite graph with non-empty parts, χ(G) = k, so the bound
becomes (k - 1) · (R(T, K_{m₁,m₂}) - 1) + m₁, where K_{m₁,m₂} is the
complete bipartite graph with part sizes m₁ (= sizes 0) and m₂ (= sizes 1).
-/
theorem erdos_problem_550 (k : ℕ) (hk : k ≥ 2) (sizes : Fin k → ℕ)
    (hsizes_pos : ∀ i, 0 < sizes i)
    (hsizes_mono : Monotone sizes) :
    let m₁ := sizes ⟨0, by omega⟩
    let m₂ := sizes ⟨1, by omega⟩
    ∃ N₀ : ℕ, ∀ (n : ℕ), n ≥ N₀ →
    ∀ (T : SimpleGraph (Fin n)), T.IsTree →
      offDiagRamseyNumber T (completeMultipartiteGraph sizes) ≤
        (k - 1) * (offDiagRamseyNumber T
          (completeMultipartiteGraph (bipSizes m₁ m₂)) - 1) + m₁ :=
  sorry

end
