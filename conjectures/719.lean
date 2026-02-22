import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Lattice

open Finset

noncomputable section

/-!
# Erdős Problem #719

Let ex_r(n; K_{r+1}^r) be the maximum number of r-edges that can be placed on
n vertices without forming a K_{r+1}^r (the r-uniform complete graph on r+1
vertices).

Is every r-hypergraph G on n vertices the union of at most ex_r(n; K_{r+1}^r)
many copies of K_r^r and K_{r+1}^r, no two of which share a K_r^r?

A conjecture of Erdős and Sauer.
-/

/-- An r-uniform hypergraph on `Fin n`: a family of r-element subsets. -/
def IsRUniformHypergraph (n r : ℕ) (H : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ H, e.card = r

/-- An r-uniform hypergraph is K_{r+1}^r-free: no (r+1)-element vertex set has
    all its r-element subsets as edges. -/
def IsHypergraphCliqueFree (r : ℕ) {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  ¬∃ S : Finset (Fin n), S.card = r + 1 ∧ Finset.powersetCard r S ⊆ H

/-- The Turán number ex_r(n; K_{r+1}^r): the maximum number of edges in an
    r-uniform K_{r+1}^r-free hypergraph on n vertices. -/
noncomputable def turanHypergraphNumber (n r : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ H : Finset (Finset (Fin n)),
    IsRUniformHypergraph n r H ∧ H.card = k ∧ IsHypergraphCliqueFree r H}

/-- The edges of a decomposition piece: if S has r elements (a K_r^r copy),
    it contributes the single edge {S}; if S has r+1 elements (a K_{r+1}^r copy),
    it contributes all r-element subsets of S. -/
def pieceEdges (r : ℕ) {n : ℕ} (S : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  if S.card = r then {S}
  else if S.card = r + 1 then Finset.powersetCard r S
  else ∅

/--
Erdős Problem #719 (Erdős-Sauer conjecture) [Er81]:

Every r-uniform hypergraph G on n vertices is the union of at most
ex_r(n; K_{r+1}^r) edge-disjoint copies of K_r^r (single edges) and K_{r+1}^r
(complete (r+1)-cliques).
-/
theorem erdos_problem_719 (n r : ℕ) (H : Finset (Finset (Fin n)))
    (hUniform : IsRUniformHypergraph n r H) :
    ∃ (pieces : Finset (Finset (Fin n))),
      (∀ S ∈ pieces, S.card = r ∨ S.card = r + 1) ∧
      (∀ e ∈ H, ∃ S ∈ pieces, e ∈ pieceEdges r S) ∧
      (∀ S ∈ pieces, ∀ e ∈ pieceEdges r S, e ∈ H) ∧
      (∀ S₁ ∈ pieces, ∀ S₂ ∈ pieces, S₁ ≠ S₂ →
        Disjoint (pieceEdges r S₁) (pieceEdges r S₂)) ∧
      pieces.card ≤ turanHypergraphNumber n r :=
  sorry

end
