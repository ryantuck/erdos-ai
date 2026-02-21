import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card

/-!
# Erdős Problem #207

For any g ≥ 2, if n is sufficiently large and n ≡ 1, 3 (mod 6), then there
exists a Steiner triple system on n vertices with girth greater than g — that is,
a 3-uniform hypergraph where every pair of vertices is in exactly one edge, and
any j edges (for 2 ≤ j ≤ g) span at least j + 3 vertices.

The congruence condition n ≡ 1, 3 (mod 6) is the necessary and sufficient
divisibility condition for a Steiner triple system on n points to exist.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].
-/

/-- A set of hyperedges forms a Steiner triple system: each edge has exactly 3
    vertices, and every pair of distinct vertices appears in exactly one edge. -/
def IsSteinerTripleSystem {n : ℕ} (edges : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ edges, e.card = 3) ∧
  (∀ u v : Fin n, u ≠ v → ∃! e, e ∈ edges ∧ u ∈ e ∧ v ∈ e)

/--
Erdős Problem #207 (Proved) [Er76]:

For any g ≥ 2, if n is sufficiently large and n ≡ 1 or 3 (mod 6), there exists
a Steiner triple system on n vertices such that any j edges (for 2 ≤ j ≤ g)
span at least j + 3 vertices.

The girth condition forbids short "cycles" in the hypergraph: any collection of
j edges (for 2 ≤ j ≤ g) must contain at least j + 3 distinct vertices.

Proved by Kwan, Sah, Sawhney, and Simkin [KSSS22b].
-/
theorem erdos_problem_207 :
    ∀ g : ℕ, 2 ≤ g →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        (n % 6 = 1 ∨ n % 6 = 3) →
          ∃ edges : Finset (Finset (Fin n)),
            IsSteinerTripleSystem edges ∧
            ∀ j : ℕ, 2 ≤ j → j ≤ g →
              ∀ S : Finset (Finset (Fin n)), S ⊆ edges → S.card = j →
                j + 3 ≤ (S.biUnion id).card :=
  sorry
