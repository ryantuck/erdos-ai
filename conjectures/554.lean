import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #554

Let R_k(G) denote the minimal m such that if the edges of K_m are k-coloured
then there is a monochromatic copy of G. Show that

  lim_{k → ∞} R_k(C_{2n+1}) / R_k(K_3) = 0

for any n ≥ 2.

A problem of Erdős and Graham [Er81c]. The problem is open even for n = 2.
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m), using Fin m arithmetic. -/
def cycleGraph (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j = i + 1 ∨ i = j + 1)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

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
Erdős Problem #554 [Er81c]:

For any n ≥ 2, lim_{k → ∞} R_k(C_{2n+1}) / R_k(K_3) = 0.

Formulated as: for every ε > 0, there exists K₀ such that for all k ≥ K₀,
  R_k(C_{2n+1}) ≤ ε · R_k(K_3).
-/
theorem erdos_problem_554 (n : ℕ) (hn : n ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      (multicolorRamseyNumber (cycleGraph (2 * n + 1) (by omega)) k : ℝ) ≤
        ε * (multicolorRamseyNumber (⊤ : SimpleGraph (Fin 3)) k : ℝ) :=
  sorry

end
