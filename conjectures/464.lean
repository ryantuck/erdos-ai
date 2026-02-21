import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational

open Set

/-- The distance of a real number from the nearest integer. -/
noncomputable def distNearestInt464 (x : ℝ) : ℝ :=
  min (Int.fract x) (1 - Int.fract x)

/-- A sequence a : ℕ → ℕ is lacunary if it is strictly increasing and there
    exists ε > 0 such that a(k+1) ≥ (1+ε) · a(k) for all k. -/
def IsLacunary464 (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧ ∃ ε : ℝ, ε > 0 ∧ ∀ k : ℕ, (a (k + 1) : ℝ) ≥ (1 + ε) * (a k : ℝ)

/--
Erdős Problem #464 (Proved by de Mathan and Pollington):

Let A = {n₁ < n₂ < ⋯} ⊂ ℕ be a lacunary sequence (there exists ε > 0 with
n_{k+1} ≥ (1+ε)n_k for all k). Then there exists an irrational θ such that
{ ‖θ nₖ‖ : k ≥ 1 } is not dense in [0, 1/2], where ‖x‖ denotes the distance
from x to the nearest integer.

The "not dense" condition is formalized as: there exist 0 ≤ c < d ≤ 1/2 such
that ‖θ nₖ‖ ∉ (c, d) for all k, i.e., the image avoids some open subinterval
of [0, 1/2].
-/
theorem erdos_problem_464 :
    ∀ (a : ℕ → ℕ), IsLacunary464 a →
    ∃ θ : ℝ, Irrational θ ∧
      ∃ c d : ℝ, 0 ≤ c ∧ c < d ∧ d ≤ 1 / 2 ∧
        ∀ k : ℕ, distNearestInt464 (θ * ↑(a k)) ∉ Set.Ioo c d :=
  sorry
