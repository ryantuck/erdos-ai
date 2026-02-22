import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

noncomputable section

open Finset

/-!
# Erdős Problem #827

Let n_k be minimal such that if n_k points in ℝ² are in general position then
there exists a subset of k points such that all C(k,3) triples determine
circles of different radii.

Determine n_k. Erdős [Er75h] asked whether n_k exists. In [Er78c] he gave a
simple argument proving existence, but the argument was incorrect as noted by
Martinez and Roldán-Pensado [MaRo15]. A corrected argument gives n_k ≪ k^9.

Tags: geometry
-/

/-- Points in ℝ² are in general position if no three are collinear. -/
def InGeneralPosition (P : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    S ⊆ P → S.card = 3 → ¬Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2)))

/-- The circumradius of three points in ℝ², defined via Heron's formula.
    For a non-degenerate triangle with side lengths a, b, c and semiperimeter
    s = (a+b+c)/2, the circumradius is R = abc / (4·√(s(s-a)(s-b)(s-c))).
    Returns 0 for degenerate (collinear) configurations. -/
noncomputable def circumradius (p₁ p₂ p₃ : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  let a := dist p₁ p₂
  let b := dist p₂ p₃
  let c := dist p₁ p₃
  let s := (a + b + c) / 2
  let area_sq := s * (s - a) * (s - b) * (s - c)
  if area_sq > 0 then
    (a * b * c) / (4 * Real.sqrt area_sq)
  else 0

/-- All C(k,3) triples of distinct points in S determine circles of pairwise
    distinct radii. -/
def AllDistinctCircumradii (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
  ∀ d ∈ S, ∀ e ∈ S, ∀ f ∈ S,
    a ≠ b → a ≠ c → b ≠ c →
    d ≠ e → d ≠ f → e ≠ f →
    ({a, b, c} : Finset _) ≠ ({d, e, f} : Finset _) →
    circumradius a b c ≠ circumradius d e f

/--
**Erdős Problem #827** [Er75h, Er78c, Er92e]:

For every k ≥ 3, there exists n such that any set of n points in ℝ² in
general position contains a k-element subset whose C(k,3) triples all
determine circumscribed circles of pairwise different radii.

Martinez and Roldán-Pensado [MaRo15] proved this with n ≤ C·k^9.
-/
theorem erdos_problem_827 (k : ℕ) (hk : k ≥ 3) :
    ∃ n : ℕ, ∀ P : Finset (EuclideanSpace ℝ (Fin 2)),
      P.card ≥ n →
      InGeneralPosition P →
      ∃ S : Finset (EuclideanSpace ℝ (Fin 2)),
        S ⊆ P ∧ S.card = k ∧ AllDistinctCircumradii S :=
  sorry

end
