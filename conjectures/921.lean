import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Walks.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #921

Let k ≥ 4 and let f_k(n) be the largest m such that there is a graph on n
vertices with chromatic number k in which every odd cycle has length > m.
Is it true that f_k(n) ≍ n^{1/(k-2)}?

A question of Erdős and Gallai [Er69b]. Gallai proved that f_4(n) ≫ n^{1/2}
and Erdős (unpublished) proved f_4(n) ≪ n^{1/2}.

This was proved for all k ≥ 4 by Kierstead, Szemerédi, and Trotter [KST84].
-/

/-- `erdos921_f k n`: the largest `m` such that there exists a graph on `n`
    vertices with chromatic number `k` in which every odd cycle has length
    `> m`. -/
noncomputable def erdos921_f (k n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    G.chromaticNumber = (k : ℕ∞) ∧
    ∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → Odd p.length → m < p.length}

/--
Erdős Problem #921, lower bound [Er69b]:

For every k ≥ 4, there exist C > 0 and N₀ such that for all n ≥ N₀,
  f_k(n) ≥ C · n^{1/(k-2)}.
-/
theorem erdos_problem_921_lower (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos921_f k n : ℝ) ≥ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2)) :=
  sorry

/--
Erdős Problem #921, upper bound [Er69b]:

For every k ≥ 4, there exist C > 0 and N₀ such that for all n ≥ N₀,
  f_k(n) ≤ C · n^{1/(k-2)}.
-/
theorem erdos_problem_921_upper (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos921_f k n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 2)) :=
  sorry

end
