import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Card

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #570

Let k ≥ 3. Is it true that, if m is sufficiently large, for any graph H
on m edges without isolated vertices,

  R(C_k, H) ≤ 2m + ⌊(k - 1) / 2⌋?

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
Erdős Problem #570 [EFRS93, p.399]:

Let k ≥ 3. For sufficiently large m, for any graph H with m edges and
no isolated vertices, R(C_k, H) ≤ 2m + ⌊(k - 1) / 2⌋.

Here C_k is the cycle on k vertices and R(G, H) is the two-colour
Ramsey number.
-/
theorem erdos_problem_570 (k : ℕ) (hk : k ≥ 3) :
    ∃ M₀ : ℕ, ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      (∀ v : Fin n, ∃ w, H.Adj v w) →
      H.edgeSet.ncard ≥ M₀ →
      ramseyNum (cycleGraph k hk) H ≤ 2 * H.edgeSet.ncard + (k - 1) / 2 :=
  sorry

end
