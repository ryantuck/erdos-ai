import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter

noncomputable section

/-!
# Erdős Problem #605

Is there some function $f(n)\to \infty$ as $n\to\infty$ such that there exist $n$ distinct
points on the surface of a two-dimensional sphere with at least $f(n)n$ many pairs of
points whose distances are the same?

This was solved by Erdős, Hickerson, and Pach [EHP89], who showed $u_{\sqrt{2}}(n) \asymp
n^{4/3}$ and $u_D(n) \gg n \log^* n$ for all $D > 1$. The lower bound was improved by
Swanepoel and Valtr [SwVa04] to $u_D(n) \gg n\sqrt{\log n}$. The best upper bound for
general $D$ is $u_D(n) \ll n^{4/3}$.

Tags: geometry, distances
-/

/-- The number of ordered pairs of distinct points from `A` at Euclidean distance `d`. -/
noncomputable def pairsAtDistance
    (A : Finset (EuclideanSpace ℝ (Fin 3))) (d : ℝ) : ℕ :=
  (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card

/--
Erdős Problem #605 [Er85]:

There exists a function f(n) → ∞ such that for all n ≥ 2, one can place n distinct
points on the surface of a sphere in ℝ³ with at least f(n) · n ordered pairs of points
at some common distance. (Equivalently, at least f(n) · n / 2 unordered pairs.)
-/
theorem erdos_problem_605 :
    ∃ f : ℕ → ℝ, Tendsto f atTop atTop ∧
      ∀ n : ℕ, n ≥ 2 →
        ∃ (R : ℝ) (A : Finset (EuclideanSpace ℝ (Fin 3))),
          R > 0 ∧ A.card = n ∧
          (∀ x ∈ A, ‖x‖ = R) ∧
          ∃ d : ℝ, (pairsAtDistance A d : ℝ) ≥ f n * n :=
  sorry

end
