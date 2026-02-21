import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Set Filter BigOperators Classical

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/--
Erdős Problem #254 [Er61]:
Let A ⊆ ℕ be such that |A ∩ [1, 2x]| - |A ∩ [1, x]| → ∞ as x → ∞, and
∑_{n ∈ A} ‖θn‖ = ∞ for every θ ∈ (0,1), where ‖x‖ denotes the distance
of x from the nearest integer. Then every sufficiently large integer is the
sum of distinct elements of A.
-/
theorem erdos_problem_254
    (A : Set ℕ)
    (hgrowth : Tendsto
      (fun x : ℕ => Set.ncard (A ∩ Set.Icc 1 (2 * x)) - Set.ncard (A ∩ Set.Icc 1 x))
      atTop atTop)
    (hsum : ∀ θ : ℝ, 0 < θ → θ < 1 →
      ¬ Summable (fun n : ℕ => if n ∈ A then distNearestInt (θ * (n : ℝ)) else 0)) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∃ S : Finset ℕ, ↑S ⊆ A ∧ ∑ x ∈ S, x = n :=
  sorry
