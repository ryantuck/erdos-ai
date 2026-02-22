import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps

open SimpleGraph

/-!
# Erdős Problem #596

For which graphs G₁, G₂ is it true that:
- for every n ≥ 1 there is a G₁-free graph H such that every n-coloring of the
  edges of H contains a monochromatic copy of G₂, and yet
- for every G₁-free graph H there is an ℵ₀-coloring of the edges of H without
  a monochromatic G₂.

Erdős and Hajnal originally conjectured that there are no such G₁, G₂, but in fact
G₁ = C₄ and G₂ = C₆ is an example. Nešetřil and Rödl established the first property
and Erdős and Hajnal the second (every C₄-free graph is a countable union of trees).

Whether this holds for G₁ = K₄ and G₂ = K₃ is the content of problem #595.

https://www.erdosproblems.com/596
-/

/-- A graph H contains a monochromatic copy of G under edge coloring c: there exists
an embedding of G into H such that all edges in the image receive the same color. -/
def SimpleGraph.HasMonochromaticCopy {W : Type*} {V : Type*}
    (H : SimpleGraph V) (G : SimpleGraph W) {α : Type*} (c : V → V → α) : Prop :=
  ∃ (φ : G ↪g H) (color : α), ∀ u v, G.Adj u v → c (φ u) (φ v) = color

/--
Erdős Problem #596 [Er87]:

There exist finite graphs G₁ and G₂ such that:
(a) For every n ≥ 1, there exists a G₁-free graph H such that every n-coloring
    of H's edges contains a monochromatic copy of G₂.
(b) For every G₁-free graph H, there exists a countable coloring of H's edges
    with no monochromatic copy of G₂.

The known example is G₁ = C₄, G₂ = C₆ (Nešetřil-Rödl for the finite Ramsey
property, Erdős-Hajnal for the countable case). The full characterization of
all such pairs remains open.
-/
theorem erdos_problem_596 :
    ∃ (W₁ : Type) (G₁ : SimpleGraph W₁) (W₂ : Type) (G₂ : SimpleGraph W₂),
      -- (a) Finite Ramsey property: for every n ≥ 1, there exists a G₁-free graph
      -- whose edges cannot be n-colored without a monochromatic G₂
      (∀ n : ℕ, 1 ≤ n →
        ∃ (V : Type) (H : SimpleGraph V),
          IsEmpty (G₁ ↪g H) ∧
          ∀ c : V → V → Fin n, H.HasMonochromaticCopy G₂ c) ∧
      -- (b) Countable failure: every G₁-free graph can be countably colored
      -- without a monochromatic G₂
      (∀ (V : Type) (H : SimpleGraph V),
        IsEmpty (G₁ ↪g H) →
        ∃ c : V → V → ℕ, ¬H.HasMonochromaticCopy G₂ c) :=
  sorry
