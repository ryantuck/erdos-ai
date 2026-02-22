import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open Finset

noncomputable section

/-!
# Erdős Problem #1076

Let k ≥ 5 and let F_k be the family of all 3-uniform hypergraphs with k vertices
and k-2 edges. Is it true that ex_3(n, F_k) ~ n²/6?

A question of Brown, Erdős, and Sós [BES73] who proved this is true for k = 4,
and that for all k ≥ 4, ex_3(n, F_k) ≍_k n².

The asymptotic version was proved independently by Bohman and Warnke [BoWa19]
and Glock, Kühn, Lo, and Osthus [GKLO20].
-/

/-- A 3-uniform hypergraph on n vertices. -/
structure Hypergraph3 (n : ℕ) where
  edges : Finset (Finset (Fin n))
  uniform : ∀ e ∈ edges, e.card = 3

/-- A 3-uniform hypergraph G on k vertices is a subhypergraph of H on n vertices
    if there is an injection from Fin k to Fin n mapping every edge of G to an edge of H. -/
def isSubhypergraph {k n : ℕ} (G : Hypergraph3 k) (H : Hypergraph3 n) : Prop :=
  ∃ f : Fin k → Fin n, Function.Injective f ∧
    ∀ e ∈ G.edges, e.image f ∈ H.edges

/-- F_k: the family of all 3-uniform hypergraphs with k vertices and exactly k-2 edges. -/
def familyF (k : ℕ) : Set (Hypergraph3 k) :=
  {G | G.edges.card = k - 2}

/-- H is F_k-free if it contains no subhypergraph from F_k. -/
def isFkFree {n : ℕ} (k : ℕ) (H : Hypergraph3 n) : Prop :=
  ∀ G : Hypergraph3 k, G ∈ familyF k → ¬isSubhypergraph G H

/-- The extremal number ex_3(n, F_k): the maximum number of edges in an F_k-free
    3-uniform hypergraph on n vertices. -/
noncomputable def ex3 (n k : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : Hypergraph3 n, isFkFree k H ∧ H.edges.card = m}

/--
Erdős Problem #1076 [BES73]:

For all k ≥ 5, ex_3(n, F_k) ~ n²/6.

Formalized as: for every ε > 0, for sufficiently large n,
  (1 - ε) · n²/6 ≤ ex_3(n, F_k) ≤ (1 + ε) · n²/6.
-/
theorem erdos_problem_1076 (k : ℕ) (hk : k ≥ 5) :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (1 - ε) * ((n : ℝ) ^ 2 / 6) ≤ (ex3 n k : ℝ) ∧
      (ex3 n k : ℝ) ≤ (1 + ε) * ((n : ℝ) ^ 2 / 6) :=
  sorry

end
