import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #569

Let k ≥ 1. What is the best possible c_k such that
  R(C_{2k+1}, H) ≤ c_k · m
for any graph H on m edges without isolated vertices?

A problem of Erdős, Faudree, Rousseau, and Schelp [EFRS93].
-/

/-- A graph G embeds into a graph H: there is an injective map from
    vertices of G to vertices of H preserving adjacency. -/
def SimpleGraph.Embeds {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, G.Adj u v → H.Adj (f u) (f v)

/-- The Ramsey number R(G, H): the minimum N such that for any graph F
    on Fin N, either G embeds in F or H embeds in the complement of F. -/
noncomputable def ramseyNum {V W : Type*}
    (G : SimpleGraph V) (H : SimpleGraph W) : ℕ :=
  sInf {N : ℕ | ∀ (F : SimpleGraph (Fin N)),
    G.Embeds F ∨ H.Embeds Fᶜ}

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/--
Erdős Problem #569 [EFRS93]:

For every k ≥ 1, there exists a constant c_k such that for any graph H
with m edges and no isolated vertices, R(C_{2k+1}, H) ≤ c_k · m.

Here C_{2k+1} is the odd cycle on 2k+1 vertices.
-/
theorem erdos_problem_569 (k : ℕ) (hk : k ≥ 1) :
    ∃ c : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      (∀ v : Fin n, ∃ w, H.Adj v w) →
      ramseyNum (cycleGraph (2 * k + 1) (by omega)) H ≤ c * H.edgeSet.ncard :=
  sorry

end
