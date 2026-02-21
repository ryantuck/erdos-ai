import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter

noncomputable section

/-!
# Erdős Problem #500

What is ex₃(n, K₄³)? That is, the largest number of 3-edges which can be placed
on n vertices so that there exists no K₄³, a set of 4 vertices which is covered
by all 4 possible 3-edges.

A problem of Turán. Turán observed that dividing the vertices into three equal
parts X₁, X₂, X₃, and taking the edges to be those triples that either have
exactly one vertex in each part or two vertices in Xᵢ and one vertex in Xᵢ₊₁
(where X₄ = X₁) shows that

  ex₃(n, K₄³) ≥ (5/9 + o(1)) C(n, 3).

This is probably the truth. The current best upper bound is

  ex₃(n, K₄³) ≤ 0.5611666 C(n, 3),

due to Razborov [Ra10].
-/

/-- A 3-uniform hypergraph on `Fin n` is K₄³-free if every edge has exactly 3
    vertices and no 4 vertices span all 4 possible 3-element subsets. -/
def IsK43Free {n : ℕ} (H : Finset (Finset (Fin n))) : Prop :=
  (∀ e ∈ H, e.card = 3) ∧
  ∀ S : Finset (Fin n), S.card = 4 → ¬(S.powersetCard 3 ⊆ H)

/-- The 3-uniform Turán number ex₃(n, K₄³): the maximum number of 3-element subsets
    of an n-element set such that no 4 vertices span all 4 triples. -/
noncomputable def ex3K43 (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Finset (Finset (Fin n)), IsK43Free H ∧ H.card = m}

/--
Erdős Conjecture (Problem #500) — Turán's Hypergraph Conjecture [Er61][Er71][Er74c][Er81]:

The 3-uniform Turán density for K₄³ is exactly 5/9. Equivalently,

  ex₃(n, K₄³) / C(n, 3) → 5/9 as n → ∞.

Turán conjectured that the lower bound construction (partition into 3 equal parts,
take triples with one vertex in each part or two in Xᵢ and one in Xᵢ₊₁) is
optimal. This remains open. The best known upper bound is ≤ 0.5611666 C(n, 3)
due to Razborov [Ra10].
-/
theorem erdos_problem_500 :
    Tendsto
      (fun n : ℕ => (ex3K43 n : ℝ) / (Nat.choose n 3 : ℝ))
      atTop (nhds (5 / 9 : ℝ)) :=
  sorry

end
