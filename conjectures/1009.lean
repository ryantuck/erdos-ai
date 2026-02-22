import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #1009

Is it true that, for every c > 0, there exists f(c) such that every graph on n
vertices with at least ⌊n²/4⌋ + k edges, where k < cn, contains at least
k - f(c) many edge disjoint triangles?

Erdős proved this for c < 1/2. Sauer showed f(2) ≥ 1. This was proved in
general by Györi [Gy88] who showed f(c) ≪ c², and also that f(c) = 0 if
c < 2 for odd n or c < 3/2 for even n.
-/

/-- A collection of `t` edge-disjoint triangles in a simple graph on `Fin n`.
    Each triangle is an injective map `Fin 3 → Fin n` whose image is a clique,
    and distinct triangles share no edge (unordered pair of vertices). -/
def HasEdgeDisjointTriangles {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  ∃ (tri : Fin t → Fin 3 → Fin n),
    (∀ i, Function.Injective (tri i)) ∧
    (∀ i (j k : Fin 3), j ≠ k → G.Adj (tri i j) (tri i k)) ∧
    (∀ i₁ i₂, i₁ ≠ i₂ →
      ∀ (j₁ k₁ : Fin 3), j₁ ≠ k₁ →
      ∀ (j₂ k₂ : Fin 3), j₂ ≠ k₂ →
        ¬((tri i₁ j₁ = tri i₂ j₂ ∧ tri i₁ k₁ = tri i₂ k₂) ∨
          (tri i₁ j₁ = tri i₂ k₂ ∧ tri i₁ k₁ = tri i₂ j₂)))

/--
Erdős Problem #1009 [Er71,p.98]:

For every c > 0, there exists f(c) such that every graph on n vertices with at
least ⌊n²/4⌋ + k edges, where k < cn, contains at least k - f(c) many edge
disjoint triangles. Proved by Györi [Gy88].
-/
theorem erdos_problem_1009 (c : ℝ) (hc : c > 0) :
    ∃ f : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    ∀ k : ℕ, (k : ℝ) < c * (n : ℝ) →
    G.edgeFinset.card ≥ n ^ 2 / 4 + k →
    HasEdgeDisjointTriangles G (k - f) :=
  sorry

end
