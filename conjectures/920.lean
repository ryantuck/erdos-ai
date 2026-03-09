import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #920

Let f_k(n) be the maximum possible chromatic number of a graph with n vertices
which contains no K_k. Is it true that, for k ≥ 4,
  f_k(n) ≫ n^{1 - 1/(k-1)} / (log n)^{c_k}
for some constant c_k > 0?

Graver and Yackel [GrYa68] proved the upper bound
  f_k(n) ≪ (n · log log n / log n)^{1 - 1/(k-1)}.

The lower bound R(4,m) ≫ m³/(log m)⁴ of Mattheus and Verstraete [MaVe23]
implies f_4(n) ≫ n^{2/3} / (log n)^{4/3}.

https://www.erdosproblems.com/920
Tags: graph theory, chromatic number
-/

/-- `erdos920_f k n`: the maximum chromatic number of a K_k-free graph on n
    vertices. Defined as the supremum over all K_k-free simple graphs on
    `Fin n` of their chromatic number (as a natural number, taking 0 when
    the chromatic number is infinite, which cannot happen for finite graphs). -/
noncomputable def erdos920_f (k n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree k ∧ G.chromaticNumber = (c : ℕ∞)}

/--
Erdős Problem #920 [Er69b]:

For every k ≥ 4, there exists a constant c_k > 0 and C > 0 such that for all
sufficiently large n,
  f_k(n) ≥ C · n^{1 - 1/(k-1)} / (log n)^{c_k}.
-/
theorem erdos_problem_920 (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧
    ∃ c : ℝ, c > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      C * (n : ℝ) ^ (1 - 1 / ((k : ℝ) - 1)) / (Real.log (n : ℝ)) ^ c
        ≤ (erdos920_f k n : ℝ) :=
  sorry

end
