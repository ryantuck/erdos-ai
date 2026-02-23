import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Classical

namespace Erdos1087

/-- A 4-element point set in ℝ² has a repeated distance if there exist two distinct
    unordered pairs of points determining the same distance. -/
def HasRepeatedDistance (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    a ≠ b ∧ c ≠ d ∧ (a ≠ c ∨ b ≠ d) ∧ (a ≠ d ∨ b ≠ c) ∧ dist a b = dist c d

/-- The number of "degenerate" 4-element subsets (those with a repeated distance)
    of a point set P in ℝ². -/
noncomputable def degenerateQuadrupleCount (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.powerset.filter (fun S => S.card = 4 ∧ HasRepeatedDistance S)).card

/--
Erdős Problem #1087 (Erdős–Purdy [ErPu71]):

Let f(n) be minimal such that every set of n points in ℝ² contains at most f(n)
"degenerate" 4-element subsets, where a 4-element subset is degenerate if some two
distinct pairs determine the same distance. Is it true that f(n) ≤ n^{3+o(1)}?

Known bounds: n³ log n ≪ f(n) ≪ n^{7/2}.

Formally: for every ε > 0 there exists N such that for all n ≥ N and every set P
of n points in ℝ², the number of degenerate quadruples is at most n^{3+ε}.
-/
theorem erdos_problem_1087 (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
        P.card = n →
        (degenerateQuadrupleCount P : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) + ε) :=
  sorry

end Erdos1087
