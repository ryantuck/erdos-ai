import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Card

/-- A 2-coloring of the edges of the complete graph on `Fin n`.
    Represented as a symmetric function assigning a color (Bool) to each pair
    of distinct vertices. -/
structure EdgeTwoColoring (n : ℕ) where
  color : Fin n → Fin n → Bool
  symm : ∀ u v : Fin n, color u v = color v u

/-- An edge {u, v} lies in a monochromatic triangle under coloring `c` if there
    exists a vertex `w` distinct from both `u` and `v` such that all three edges
    {u,v}, {u,w}, {v,w} have the same color. -/
def EdgeTwoColoring.inMonoTriangle {n : ℕ} (c : EdgeTwoColoring n)
    (u v : Fin n) : Prop :=
  ∃ w : Fin n, w ≠ u ∧ w ≠ v ∧
    c.color u v = c.color u w ∧ c.color u v = c.color v w

/-- The number of edges of K_n (counted as unordered pairs with u < v) that
    do not lie in any monochromatic triangle under coloring `c`. -/
noncomputable def edgesNotInMonoTriangleCount {n : ℕ} (c : EdgeTwoColoring n) : ℕ :=
  Set.ncard {p : Fin n × Fin n | p.1 < p.2 ∧ ¬c.inMonoTriangle p.1 p.2}

/--
Erdős Problem #639 [Er97d]:
If the edges of K_n are 2-coloured then there are at most ⌊n²/4⌋ edges
which do not occur in a monochromatic triangle.

Solved by Keevash and Sudakov [KeSu04], who proved the threshold is exactly
⌊n²/4⌋ for all n ≥ 7.
-/
theorem erdos_problem_639 (n : ℕ) (hn : 7 ≤ n) (c : EdgeTwoColoring n) :
    edgesNotInMonoTriangleCount c ≤ n ^ 2 / 4 :=
  sorry
