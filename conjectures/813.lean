import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Classical

noncomputable section

/-!
# Erdős Problem #813

Let h(n) be minimal such that every graph on n vertices where every set of
7 vertices contains a triangle (a copy of K₃) must contain a clique on at
least h(n) vertices. Estimate h(n) — in particular, do there exist constants
c₁, c₂ > 0 such that

  n^{1/3 + c₁} ≪ h(n) ≪ n^{1/2 - c₂}?

A problem of Erdős and Hajnal [Er91], who proved n^{1/3} ≪ h(n) ≪ n^{1/2}.
Bucić and Sudakov [BuSu23] proved h(n) ≫ n^{5/12 - o(1)}.
-/

/-- A graph on `Fin n` has the property that every subset of 7 vertices
    contains a triangle (three mutually adjacent vertices). -/
def EverySevenSetHasTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), S.card = 7 →
    ∃ a b c, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.Adj a b ∧ G.Adj a c ∧ G.Adj b c

/-- The clique number of a graph on `Fin n`: the supremum of sizes of cliques. -/
noncomputable def graphCliqueNumber {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset (Fin n), S.card = k ∧ G.IsClique (↑S : Set (Fin n))}

/-- h(n) is the minimum clique number over all graphs on n vertices in which
    every set of 7 vertices contains a triangle. -/
noncomputable def erdos813_h (n : ℕ) : ℕ :=
  sInf (graphCliqueNumber '' {G : SimpleGraph (Fin n) | EverySevenSetHasTriangle G})

/--
Erdős Problem #813 [Er91]:

There exist constants c₁, c₂ > 0 such that for all sufficiently large n,
  C₁ · n^{1/3 + c₁} ≤ h(n) ≤ C₂ · n^{1/2 - c₂}.
-/
theorem erdos_problem_813 :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ C₁ : ℝ, C₁ > 0 ∧
    ∃ C₂ : ℝ, C₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C₁ * (n : ℝ) ^ ((1 : ℝ) / 3 + c₁) ≤ (erdos813_h n : ℝ) ∧
      (erdos813_h n : ℝ) ≤ C₂ * (n : ℝ) ^ ((1 : ℝ) / 2 - c₂) :=
  sorry

end
