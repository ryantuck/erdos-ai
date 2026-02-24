import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Basic

/-!
# Erdős Problem #76

In any 2-colouring of the edges of K_n there must exist at least
(1 + o(1)) n²/12 many edge-disjoint monochromatic triangles.

Conjectured by Erdős, Faudree, and Ordman. Proved by Gruslys and Letzter [GrLe20].

The bound is tight: partition V(K_n) into two equal halves, colour edges
between parts red and edges within parts blue — any edge-disjoint monochromatic
triangle must either use 3 blue edges (within a part) or 3 red edges (between
parts), and a careful count shows ≈ n²/12 is achievable but not more.
-/

/-- A 2-edge-colouring of K_n assigns a Bool to each unordered pair of vertices.
    (Values at diagonal elements ⟦(v, v)⟧ are irrelevant.) -/
def EdgeTwoColoring (n : ℕ) := Sym2 (Fin n) → Bool

/-- The set of (non-diagonal) edges of a triangle T ⊆ V(K_n):
    all unordered pairs {x, y} with x ≠ y and x, y ∈ T. -/
def triangleEdges {n : ℕ} (T : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  ((T ×ˢ T).image (fun p : Fin n × Fin n => s(p.1, p.2))).filter (fun e => ¬e.IsDiag)

/-- A 3-vertex set T ⊆ V(K_n) is a monochromatic triangle under colouring col if
    all three edges of T receive the same colour. -/
def IsMonochromaticTriangle {n : ℕ} (col : EdgeTwoColoring n) (T : Finset (Fin n)) : Prop :=
  T.card = 3 ∧ ∃ c : Bool, ∀ e ∈ triangleEdges T, col e = c

/-- A family 𝒯 of triangles is edge-disjoint if any two distinct triangles in 𝒯
    share no edge. -/
def IsEdgeDisjointFamily {n : ℕ} (𝒯 : Finset (Finset (Fin n))) : Prop :=
  ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → Disjoint (triangleEdges T₁) (triangleEdges T₂)

/--
**Erdős Problem #76** (Erdős–Faudree–Ordman conjecture, proved by Gruslys–Letzter [GrLe20]):

In any 2-colouring of the edges of K_n, there exist at least (1 + o(1)) n²/12
edge-disjoint monochromatic triangles.

Formally: for every ε > 0 there exists N such that for all n ≥ N and any
2-colouring col of the edges of K_n, there is an edge-disjoint family of
monochromatic triangles of size at least (1 - ε) · n² / 12.
-/
theorem erdos_problem_76 :
    ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ col : EdgeTwoColoring n,
    ∃ 𝒯 : Finset (Finset (Fin n)),
      (∀ T ∈ 𝒯, IsMonochromaticTriangle col T) ∧
      IsEdgeDisjointFamily 𝒯 ∧
      (1 - ε) * (n : ℝ) ^ 2 / 12 ≤ (𝒯.card : ℝ) :=
  sorry
