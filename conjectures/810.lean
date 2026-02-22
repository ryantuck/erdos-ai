import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #810

Does there exist some ε > 0 such that, for all sufficiently large n, there
exists a graph G on n vertices with at least εn² many edges such that the
edges can be coloured with n colours so that every C₄ receives 4 distinct
colours?

A problem of Burr, Erdős, Graham, and Sós.
-/

/-- A graph on n vertices admits a rainbow C₄ coloring with n colors if there
    exists an edge coloring using n colors such that every 4-cycle in the
    graph has all 4 edges receiving distinct colors. -/
def AdmitsRainbowC4Coloring (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ c : Sym2 (Fin n) → Fin n,
    ∀ (a b d e : Fin n),
      a ≠ b → a ≠ d → a ≠ e → b ≠ d → b ≠ e → d ≠ e →
      G.Adj a b → G.Adj b d → G.Adj d e → G.Adj e a →
      c (Sym2.mk (a, b)) ≠ c (Sym2.mk (b, d)) ∧
      c (Sym2.mk (a, b)) ≠ c (Sym2.mk (d, e)) ∧
      c (Sym2.mk (a, b)) ≠ c (Sym2.mk (e, a)) ∧
      c (Sym2.mk (b, d)) ≠ c (Sym2.mk (d, e)) ∧
      c (Sym2.mk (b, d)) ≠ c (Sym2.mk (e, a)) ∧
      c (Sym2.mk (d, e)) ≠ c (Sym2.mk (e, a))

/--
**Erdős Problem #810**: Does there exist some ε > 0 such that, for all
sufficiently large n, there exists a graph G on n vertices with at least εn²
many edges such that the edges can be coloured with n colours so that every
C₄ receives 4 distinct colours?
-/
theorem erdos_problem_810_conjecture :
    ∃ ε : ℝ, 0 < ε ∧
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∃ G : SimpleGraph (Fin n),
        (G.edgeSet.ncard : ℝ) ≥ ε * (n : ℝ) ^ 2 ∧
        AdmitsRainbowC4Coloring n G :=
  sorry

end
