import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #1158

Let K_t(r) be the complete t-partite t-uniform hypergraph with r vertices
in each class.

Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)} for all t, r?

Erdős [Er64f] proved that
n^{t - O(r^{1-t})} ≤ ex_t(n, K_t(r)) ≪ n^{t - r^{1-t}}.
This is only known when t = 2 and 2 ≤ r ≤ 3. The case t = 2 is problem #714.

Reference: [Va99, 3.65]

Tags: hypergraphs, turan number
-/

/-- A t-uniform hypergraph on Fin n: every edge has exactly t vertices. -/
def IsUniformHypergraph1158 (t : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ E, e.card = t

/-- A t-uniform hypergraph E on Fin n contains a copy of the complete t-partite
    t-uniform hypergraph K_t(r) if there exist t pairwise disjoint vertex classes,
    each of size r, such that every transversal forms an edge of E. -/
def HasKtrCopy1158 (t r : ℕ) {n : ℕ} (E : Finset (Finset (Fin n))) : Prop :=
  ∃ classes : Fin t → Finset (Fin n),
    (∀ i, (classes i).card = r) ∧
    (∀ i j, i ≠ j → Disjoint (classes i) (classes j)) ∧
    (∀ f : Fin t → Fin n, (∀ i, f i ∈ classes i) →
      Finset.image f Finset.univ ∈ E)

/--
**Erdős Problem #1158** [Va99, 3.65]:

Let K_t(r) be the complete t-partite t-uniform hypergraph with r vertices in
each class. Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)} for all t, r?

Formally: for all t ≥ 2, r ≥ 2, and ε > 0, for sufficiently large n, there exists
a t-uniform hypergraph on n vertices with no K_t(r) copy and at least
n^{t - r^{1-t} - ε} edges.
-/
theorem erdos_problem_1158 :
    ∀ (t r : ℕ), 2 ≤ t → 2 ≤ r →
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ E : Finset (Finset (Fin n)),
        IsUniformHypergraph1158 t E ∧
        ¬HasKtrCopy1158 t r E ∧
        (E.card : ℝ) ≥ (n : ℝ) ^ ((t : ℝ) - (r : ℝ) ^ (1 - (t : ℝ)) - ε) := by
  sorry

end
