import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Complex BigOperators Finset

noncomputable section

/-!
# Erdős Problem #256

Let n ≥ 1 and f(n) be maximal such that for any integers 1 ≤ a₁ ≤ ⋯ ≤ aₙ,
  max_{|z|=1} |∏ᵢ (1 - z^{aᵢ})| ≥ f(n).

Equivalently, f(n) is the infimum over all non-decreasing sequences of positive
integers (a₁, ..., aₙ) of the supremum of |∏ᵢ (1 - z^{aᵢ})| over the unit
circle.

Erdős conjectured that there exists c > 0 such that log f(n) ≫ n^c.

This specific conjecture was answered negatively by Belov and Konyagin [BeKo96],
who proved that log f(n) ≪ (log n)⁴. The broader problem of precisely
estimating f(n) remains open.
-/

/-- The supremum of |∏ᵢ (1 - z^{aᵢ})| as z ranges over the unit circle,
    for a fixed sequence of exponents a. -/
noncomputable def unitCircleMaxProd (n : ℕ) (a : Fin n → ℕ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℂ, ‖z‖ = 1 ∧
    y = ‖∏ i : Fin n, (1 - z ^ (a i))‖}

/-- f(n) is the largest real number such that for any positive integers
    1 ≤ a₁ ≤ ⋯ ≤ aₙ, the maximum of |∏ᵢ (1 - z^{aᵢ})| on the unit circle
    is at least f(n). Equivalently, the infimum of unitCircleMaxProd over
    all non-decreasing sequences of positive integers of length n. -/
noncomputable def erdos256_f (n : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ (a : Fin n → ℕ),
    (∀ i, 0 < a i) ∧ Monotone a ∧
    y = unitCircleMaxProd n a}

/--
Erdős Conjecture (Problem #256) [Er61, Er64b]:

There exists a constant c > 0 such that log f(n) ≫ n^c, i.e., there exist
constants c > 0 and C > 0 such that for all sufficiently large n,
  log f(n) ≥ C · n^c.

Note: This was answered negatively by Belov and Konyagin [BeKo96], who showed
log f(n) ≪ (log n)⁴. The problem of estimating f(n) precisely remains open.
-/
theorem erdos_problem_256 :
    ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      Real.log (erdos256_f n) ≥ C * (n : ℝ) ^ c :=
  sorry

end
