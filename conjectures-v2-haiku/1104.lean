import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open SimpleGraph Real

noncomputable section

/-!
# Erdős Problem #1104

Let f(n) be the maximum possible chromatic number of a triangle-free graph on
n vertices. Estimate f(n).

The best bounds available are
  (1 - o(1))(n / log n)^{1/2} ≤ f(n) ≤ (2 + o(1))(n / log n)^{1/2}.
The upper bound is due to Davies and Illingworth [DaIl22], the lower bound
follows from a construction of Hefty, Horn, King, and Pfender [HHKP25].

The function f(n) is the inverse to the function h₃(k) considered in [1013].
A generalisation of f(n) is considered in [920].

https://www.erdosproblems.com/1104
Tags: graph theory, chromatic number
-/

/-- `erdos1104_f n`: the maximum chromatic number of a triangle-free graph on n
    vertices. Defined as the supremum over all triangle-free simple graphs on
    `Fin n` of their chromatic number. -/
noncomputable def erdos1104_f (n : ℕ) : ℕ :=
  sSup {c : ℕ | ∃ G : SimpleGraph (Fin n),
    G.CliqueFree 3 ∧ G.chromaticNumber = (c : ℕ∞)}

/--
Erdős Problem #1104 [Er67c]:

There exist constants c₁, c₂ > 0 such that for all sufficiently large n,
  c₁ · (n / log n)^{1/2} ≤ f(n) ≤ c₂ · (n / log n)^{1/2}.
-/
theorem erdos_problem_1104 :
    ∃ c₁ : ℝ, c₁ > 0 ∧
    ∃ c₂ : ℝ, c₂ > 0 ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      c₁ * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2)
        ≤ (erdos1104_f n : ℝ) ∧
      (erdos1104_f n : ℝ)
        ≤ c₂ * ((n : ℝ) / Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

end
