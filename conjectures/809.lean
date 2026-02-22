import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #809

Let k ≥ 3 and define F_k(n) to be the minimal r such that there is a graph G
on n vertices with ⌊n²/4⌋+1 edges such that the edges can be r-coloured so
that every subgraph isomorphic to C_{2k+1} has no colour repeating on the edges.

Is it true that F_k(n) ~ n²/8?

A problem of Burr, Erdős, Graham, and Sós, who proved that F_k(n) ≫ n².
-/

/-- There exists a graph on n vertices with ⌊n²/4⌋+1 edges admitting an
    r-edge-coloring such that every cycle of length 2k+1 is rainbow
    (no repeated edge colors). -/
def AdmitsRainbowOddCycleColoring (k n r : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n),
    G.edgeSet.ncard = n ^ 2 / 4 + 1 ∧
    ∃ c : Sym2 (Fin n) → Fin r,
      ∀ (f : Fin (2 * k + 1) → Fin n),
        Function.Injective f →
        (∀ i : Fin (2 * k + 1),
          G.Adj (f i) (f ⟨(i.val + 1) % (2 * k + 1),
            Nat.mod_lt _ (by omega)⟩)) →
        Function.Injective (fun i : Fin (2 * k + 1) =>
          c (Sym2.mk (f i, f ⟨(i.val + 1) % (2 * k + 1),
            Nat.mod_lt _ (by omega)⟩)))

/--
**Erdős Problem #809**: F_k(n) ~ n²/8 for all k ≥ 3.

For every ε > 0, for sufficiently large n, F_k(n) lies between
(1-ε)n²/8 and (1+ε)n²/8.
-/
theorem erdos_problem_809_conjecture (k : ℕ) (hk : k ≥ 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (∃ r : ℕ, (↑r : ℝ) ≤ (1 + ε) * ↑n ^ 2 / 8 ∧
        AdmitsRainbowOddCycleColoring k n r) ∧
      (∀ r : ℕ, (↑r : ℝ) < (1 - ε) * ↑n ^ 2 / 8 →
        ¬AdmitsRainbowOddCycleColoring k n r) :=
  sorry

end
