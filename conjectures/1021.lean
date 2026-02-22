import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #1021

Is it true that, for every k ≥ 3, there is a constant c_k > 0 such that
  ex(n, G_k) ≪ n^{3/2 - c_k},
where G_k is the 1-subdivision of K_k: the bipartite graph between
{y₁, …, y_k} and {z₁, …, z_{k choose 2}}, with each z_j joined to a
unique pair of yᵢ?

A conjecture of Erdős and Simonovits [Er71,p.103][Er74c,p.79]. This was
proved by Conlon and Lee [CoLe21] with c_k = 6^{-k}, later improved to
c_k = 1/(4k-6) by Janzer [Ja19].
-/

/-- Adjacency in the 1-subdivision of K_k. Vertices are "original" (Fin k) or
    "edge" ({(i,j) : i < j}). Each edge-vertex is adjacent to exactly its two
    original endpoints. -/
def subdivKAdj (k : ℕ) :
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} →
    Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2} → Prop
  | .inl a, .inr ⟨⟨i, j⟩, _⟩ => a = i ∨ a = j
  | .inr ⟨⟨i, j⟩, _⟩, .inl a => a = i ∨ a = j
  | _, _ => False

/-- The 1-subdivision of K_k. The vertex set is the disjoint union of the
    k original vertices and the (k choose 2) edge-subdivision vertices.
    Each edge-vertex is adjacent to exactly the two endpoints of its
    corresponding edge in K_k. -/
def subdivisionKComplete (k : ℕ) :
    SimpleGraph (Fin k ⊕ {p : Fin k × Fin k // p.1 < p.2}) where
  Adj := subdivKAdj k
  symm := by
    intro v w h
    rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> rcases w with b | ⟨⟨i', j'⟩, hij'⟩ <;> exact h
  loopless := ⟨fun v h => by rcases v with a | ⟨⟨i, j⟩, hij⟩ <;> exact h⟩

/-- A graph G contains H as a subgraph if there is an injective vertex map
    that sends edges to edges. -/
def containsSubgraph {V W : Type*} (G : SimpleGraph V)
    (H : SimpleGraph W) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/--
Erdős Problem #1021 [Er71,p.103][Er74c,p.79]:

For every k ≥ 3, there exists c_k > 0 and C > 0 such that every n-vertex
graph not containing the 1-subdivision of K_k as a subgraph has at most
C · n^{3/2 - c_k} edges.

Proved by Conlon and Lee [CoLe21] with c_k = 6^{-k}. Improved to
c_k = 1/(4k-6) by Janzer [Ja19].
-/
theorem erdos_problem_1021 (k : ℕ) (hk : k ≥ 3) :
    ∃ (c : ℝ), c > 0 ∧ ∃ (C : ℝ), C > 0 ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ¬containsSubgraph G (subdivisionKComplete k) →
    (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2 - c) :=
  sorry

end
