import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #837

Let k ≥ 2 and A_k ⊆ [0,1] be the set of α such that there exists some
β(α) > α with the property that, if G₁, G₂, … is a sequence of k-uniform
hypergraphs with

  liminf e(Gₙ) / C(|Gₙ|, k) > α

then there exist subgraphs Hₙ ⊆ Gₙ such that |Hₙ| → ∞ and

  liminf e(Hₙ) / C(|Hₙ|, k) > β,

and further that this property does not necessarily hold if > α is
replaced by ≥ α.

It is known that A₂ = {1 - 1/m : m ≥ 1} (Erdős-Stone-Simonovits).

What is A₃?

A problem of Erdős and Simonovits [Er74d].
-/

/-- A k-uniform hypergraph on n vertices: a collection of k-element subsets
    of Fin n. -/
structure UniformHypergraph (n k : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = k

/-- The edge density of a k-uniform hypergraph: |edges| / C(n, k). -/
noncomputable def UniformHypergraph.density {n k : ℕ}
    (G : UniformHypergraph n k) : ℝ :=
  if Nat.choose n k = 0 then 0
  else (G.edges.card : ℝ) / (Nat.choose n k : ℝ)

/-- H is a sub-hypergraph of G via an injective vertex map f,
    meaning every edge of H maps to an edge of G under f. -/
def UniformHypergraph.IsSubgraphVia {m n k : ℕ} (H : UniformHypergraph m k)
    (G : UniformHypergraph n k) (f : Fin m ↪ Fin n) : Prop :=
  ∀ e ∈ H.edges, e.map f ∈ G.edges

/-- The density jump set A_k for k-uniform hypergraphs.
    α ∈ A_k iff there exists β > α such that:
    (a) any sequence of k-uniform hypergraphs with liminf density > α
        contains growing subgraphs with liminf density > β;
    (b) this does NOT hold when the hypothesis is weakened to liminf density ≥ α. -/
def densityJumpSet (k : ℕ) : Set ℝ :=
  {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧
    ∃ β : ℝ, β > α ∧
      -- (a) Density jump: liminf density > α implies dense growing subgraphs
      (∀ (sizes : ℕ → ℕ) (G : ∀ i, UniformHypergraph (sizes i) k),
        -- Hypothesis: liminf density(Gᵢ) > α
        (∃ δ : ℝ, δ > 0 ∧ ∃ N₀ : ℕ, ∀ i : ℕ, i ≥ N₀ →
          (G i).density ≥ α + δ) →
        -- Conclusion: ∃ subgraphs Hᵢ with |Hᵢ| → ∞ and liminf density > β
        ∃ (subSizes : ℕ → ℕ) (H : ∀ i, UniformHypergraph (subSizes i) k),
          (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → subSizes i ≥ M) ∧
          (∀ i, ∃ f : Fin (subSizes i) ↪ Fin (sizes i),
            (H i).IsSubgraphVia (G i) f) ∧
          (∃ δ' : ℝ, δ' > 0 ∧ ∃ N₁ : ℕ, ∀ i : ℕ, i ≥ N₁ →
            (H i).density ≥ β + δ')) ∧
      -- (b) Fails with ≥ α: ∃ counterexample sequence with liminf density ≥ α
      --     but no dense growing subgraphs with density > β
      ¬(∀ (sizes : ℕ → ℕ) (G : ∀ i, UniformHypergraph (sizes i) k),
        -- Hypothesis: liminf density(Gᵢ) ≥ α
        (∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ i : ℕ, i ≥ N₀ →
          (G i).density ≥ α - ε) →
        ∃ (subSizes : ℕ → ℕ) (H : ∀ i, UniformHypergraph (subSizes i) k),
          (∀ M : ℕ, ∃ N : ℕ, ∀ i : ℕ, i ≥ N → subSizes i ≥ M) ∧
          (∀ i, ∃ f : Fin (subSizes i) ↪ Fin (sizes i),
            (H i).IsSubgraphVia (G i) f) ∧
          (∃ δ' : ℝ, δ' > 0 ∧ ∃ N₁ : ℕ, ∀ i : ℕ, i ≥ N₁ →
            (H i).density ≥ β + δ'))}

/-- Known: A₂ = {1 - 1/m : m ≥ 1} (Erdős-Stone-Simonovits density jump). -/
theorem erdos_densityJumpSet_graphs :
    densityJumpSet 2 = {α : ℝ | ∃ m : ℕ, m ≥ 1 ∧ α = 1 - 1 / (m : ℝ)} :=
  sorry

/--
Erdős Problem #837 (OPEN) [Er74d]:

Determine the density jump set A₃ for 3-uniform hypergraphs.

It is known that A₂ = {1 - 1/m : m ≥ 1} by the Erdős-Stone-Simonovits theorem.
The analogous characterization of A₃ is open.
-/
theorem erdos_problem_837 :
    densityJumpSet 3 = (sorry : Set ℝ) :=
  sorry

end
