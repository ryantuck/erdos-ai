import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic

open SimpleGraph

noncomputable section

/-!
# Erdős Problem #1013

Let h₃(k) be the minimal n such that there exists a triangle-free graph on n
vertices with chromatic number k. Find an asymptotic for h₃(k), and also prove
  lim_{k → ∞} h₃(k+1) / h₃(k) = 1.

The function h₃(k) is dual to the function f(n) considered in [1104], in that
h₃(k) = n if and only if n is minimal such that f(n) = k.

Known bounds (from [1104]):
  (1/2 - o(1)) k² log k ≤ h₃(k) ≤ (1 + o(1)) k² log k.

Tags: graph theory, chromatic number
-/

/-- `h3 k` is the minimum number of vertices `n` such that there exists a
    triangle-free graph on `n` vertices with chromatic number exactly `k`. -/
def h3 (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ G : SimpleGraph (Fin n), G.CliqueFree 3 ∧ G.chromaticNumber = (k : ℕ∞)}

/--
Erdős Problem #1013 [Er71]:

lim_{k → ∞} h₃(k+1) / h₃(k) = 1,

where h₃(k) is the minimum number of vertices of a triangle-free graph with
chromatic number k.

Formulated as: for every ε > 0, there exists K₀ such that for all k ≥ K₀,
  |h₃(k+1) / h₃(k) - 1| ≤ ε.
-/
theorem erdos_problem_1013 :
    ∀ ε : ℝ, ε > 0 →
    ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
      |(h3 (k + 1) : ℝ) / (h3 k : ℝ) - 1| ≤ ε :=
  sorry

end
