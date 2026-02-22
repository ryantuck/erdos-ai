import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #556

Let R_3(G) denote the minimal m such that if the edges of K_m are 3-coloured
then there must be a monochromatic copy of G. Show that
  R_3(C_n) ≤ 4n - 3.

A problem of Bondy and Erdős. This inequality is best possible for odd n.
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The k-colour Ramsey number R_k(G): the minimum N such that for every
    k-colouring of the edges of K_N, there is a monochromatic copy of G.

    A k-colouring is a symmetric function c : Fin N → Fin N → Fin k.
    A monochromatic copy of G in colour a is an injective map f : V → Fin N
    such that every edge of G maps to an edge of colour a. -/
noncomputable def multicolorRamseyNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ (c : Fin N → Fin N → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a : Fin k) (f : V → Fin N), Function.Injective f ∧
      ∀ u v, G.Adj u v → c (f u) (f v) = a}

/--
Erdős Problem #556 [Er81][Er81c]:

For all n ≥ 3, the 3-colour Ramsey number of the cycle C_n satisfies
  R_3(C_n) ≤ 4n - 3.
-/
theorem erdos_problem_556 (n : ℕ) (hn : n ≥ 3) :
    multicolorRamseyNumber (cycleGraph n hn) 3 ≤ 4 * n - 3 :=
  sorry

end
