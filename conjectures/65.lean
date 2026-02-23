import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open SimpleGraph Finset

/-- The complete bipartite graph K_{a,b} on Fin (a + b), where vertices {0,…,a-1} form one
    part and {a,…,a+b-1} form the other. -/
def completeBipartiteGraph65 (a b : ℕ) : SimpleGraph (Fin (a + b)) where
  Adj u v := (u.val < a ∧ a ≤ v.val) ∨ (a ≤ u.val ∧ v.val < a)
  symm u v h := by
    rcases h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  loopless := ⟨fun v h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega⟩

/--
Erdős Problem #65 (Erdős-Hajnal):
Let G be a graph with n vertices and kn edges, and a₁ < a₂ < ⋯ be the distinct lengths
of cycles in G. Is it true that ∑ 1/aᵢ ≫ log k? Is the sum ∑ 1/aᵢ minimised when G is
a complete bipartite graph?

The first question was proved by Gyárfás, Komlós, and Szemerédi [GKS84].
Liu and Montgomery [LiMo20] proved the asymptotically sharp lower bound ≥ (1/2 - o(1)) log k.

The remaining open question is formalized below: for any graph G on n vertices whose edge
count equals a * b for some partition a + b = n, the sum of reciprocals of distinct cycle
lengths of G is at least the corresponding sum for the complete bipartite graph K_{a,b}.
-/
theorem erdos_problem_65 {n : ℕ}
    (G : SimpleGraph (Fin n))
    (a b : ℕ) (hab : a + b = n) [DecidableRel G.Adj]
    (hedge : a * b = G.edgeFinset.card)
    (T_G : Finset ℕ)
    (hT_sub : ∀ m ∈ T_G, ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m)
    (hT_sup : ∀ m : ℕ, (∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_G) :
    ∃ (T_K : Finset ℕ),
      (∀ m ∈ T_K, ∃ v : Fin (a + b),
        ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) ∧
      (∀ m : ℕ, (∃ v : Fin (a + b),
        ∃ p : (completeBipartiteGraph65 a b).Walk v v, p.IsCycle ∧ p.length = m) → m ∈ T_K) ∧
      ∑ m ∈ T_K, (1 / (m : ℝ)) ≤ ∑ m ∈ T_G, (1 / (m : ℝ)) :=
  sorry
