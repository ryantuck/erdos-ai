import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

noncomputable section

/- !
# Erdős Problem #716

Let $\mathcal{F}$ be the family of all $3$-uniform hypergraphs with $6$ vertices
and $3$ $3$-edges. Is it true that $\mathrm{ex}_3(n,\mathcal{F})=o(n^2)$?

This is a conjecture of Brown, Erdős, and Sós [BES73]. The answer is yes,
proved by Ruzsa and Szemerédi [RuSz78] (known as the Ruzsa-Szemerédi problem).
-/

/-- A 3-uniform hypergraph on `Fin n`: a family of 3-element subsets. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph is F-free (where F is the family of all 3-uniform
    hypergraphs on 6 vertices with 3 edges) if every 6-element subset of
    vertices contains at most 2 edges. -/
def Hypergraph3.isFree {n : ℕ} (H : Hypergraph3 n) : Prop :=
  ∀ S : Finset (Fin n), S.card = 6 →
    (H.edges.filter (· ⊆ S)).card ≤ 2

/-- **Erdős Problem #716** (Brown-Erdős-Sós conjecture, proved by Ruzsa-Szemerédi):
    ex₃(n, F) = o(n²), i.e., for any ε > 0, every sufficiently large F-free
    3-uniform hypergraph on n vertices has at most ε·n² edges. -/
theorem erdos_problem_716 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : Hypergraph3 n, H.isFree →
    (H.edges.card : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
  sorry
