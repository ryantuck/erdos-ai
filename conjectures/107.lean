import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Set

/-- Points in ℝ² are in **general position** if no three are collinear. -/
def GeneralPosition (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ p₁ ∈ S, ∀ p₂ ∈ S, ∀ p₃ ∈ S,
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬Collinear ℝ ({p₁, p₂, p₃} : Set (Fin 2 → ℝ))

/-- A finite set of points in ℝ² is in **convex position** if every point
is an extreme point of the convex hull of the set. -/
def ConvexPosition (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∀ p ∈ S, p ∈ (convexHull ℝ (↑S : Set (Fin 2 → ℝ))).extremePoints ℝ

/--
Erdős Problem #107 [Er61, Er75f, Er81, Er82e, Er83c, Er95, Er97c, Er97e, Va99]:

The Erdős-Klein-Szekeres 'Happy Ending' problem. Let f(n) be minimal such that
any f(n) points in ℝ², no three on a line, contain n points which form the
vertices of a convex n-gon. Prove that f(n) = 2^{n-2} + 1.

The lower bound f(n) ≥ 2^{n-2} + 1 was proved by Erdős and Szekeres [ErSz60].
The upper bound f(n) ≤ C(2n-4, n-2) + 1 was proved in [ErSz35], with the best
current bound f(n) ≤ 2^{n+O(√(n log n))} due to Holmsen, Mojarrad, Pach, and
Tardos [HMPT20].
-/
theorem erdos_problem_107 (n : ℕ) (hn : n ≥ 3) :
    (∀ (S : Finset (Fin 2 → ℝ)),
      S.card ≥ 2 ^ (n - 2) + 1 →
      GeneralPosition S →
      ∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T) ∧
    (∃ (S : Finset (Fin 2 → ℝ)),
      S.card = 2 ^ (n - 2) ∧
      GeneralPosition S ∧
      ¬∃ T : Finset (Fin 2 → ℝ), T ⊆ S ∧ T.card = n ∧ ConvexPosition T) :=
  sorry
