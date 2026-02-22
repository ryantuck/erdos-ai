import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #584

Let G be a graph with n vertices and δn² edges. Are there subgraphs H₁, H₂ ⊆ G such that:
1. H₁ has ≫ δ³n² edges and every two edges in H₁ are contained in a cycle
   (in G) of length at most 6, and furthermore if two edges share a vertex
   they are on a cycle of length 4, and
2. H₂ has ≫ δ²n² edges and every two edges in H₂ are contained in a cycle
   (in G) of length at most 8.

A problem of Erdős, Duke, and Rödl [DuEr82, DER84].
-/

/-- Two edges of a graph lie on a common cycle of length at most `k`. -/
def edgesOnCommonCycle {V : Type*} (G : SimpleGraph V)
    (e₁ e₂ : Sym2 V) (k : ℕ) : Prop :=
  ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ c.length ≤ k ∧
    e₁ ∈ c.edges ∧ e₂ ∈ c.edges

/-- Two edges share a vertex. -/
def edgesShareVertex {V : Type*} (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v : V, v ∈ e₁ ∧ v ∈ e₂

/--
Erdős Problem #584, Part 1:
For every graph G on n vertices with δn² edges, there exists a subgraph H₁
with ≫ δ³n² edges such that every two edges of H₁ lie on a common cycle of
length at most 6 in G, and any two edges sharing a vertex lie on a common
cycle of length 4.
-/
theorem erdos_problem_584_part1 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ δ * (n : ℝ) ^ 2 →
      ∃ H : SimpleGraph (Fin n),
        H ≤ G ∧
        (H.edgeFinset.card : ℝ) ≥ c * δ ^ 3 * (n : ℝ) ^ 2 ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          edgesOnCommonCycle G e₁ e₂ 6) ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          edgesShareVertex e₁ e₂ → edgesOnCommonCycle G e₁ e₂ 4) :=
  sorry

/--
Erdős Problem #584, Part 2:
For every graph G on n vertices with δn² edges, there exists a subgraph H₂
with ≫ δ²n² edges such that every two edges of H₂ lie on a common cycle of
length at most 8 in G.
-/
theorem erdos_problem_584_part2 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n : ℕ), 0 < n →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (G : SimpleGraph (Fin n)),
      (G.edgeFinset.card : ℝ) ≥ δ * (n : ℝ) ^ 2 →
      ∃ H : SimpleGraph (Fin n),
        H ≤ G ∧
        (H.edgeFinset.card : ℝ) ≥ c * δ ^ 2 * (n : ℝ) ^ 2 ∧
        (∀ e₁ ∈ H.edgeFinset, ∀ e₂ ∈ H.edgeFinset,
          edgesOnCommonCycle G e₁ e₂ 8) :=
  sorry
