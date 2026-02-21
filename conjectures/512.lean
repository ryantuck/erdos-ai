import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset BigOperators MeasureTheory

noncomputable section

/-!
# Erdős Problem #512 (PROVED)

Is it true that, if $A \subset \mathbb{Z}$ is a finite set of size $N$, then
$$\int_0^1 \left| \sum_{n \in A} e(n\theta) \right| d\theta \gg \log N,$$
where $e(x) = e^{2\pi i x}$?

This is Littlewood's conjecture, proved independently by Konyagin [Ko81]
and McGehee, Pigno, and Smith [MPS81].
-/

/-- The exponential sum ∑_{n ∈ A} e(nθ) where e(x) = e^{2πix}. -/
def expSum512 (A : Finset ℤ) (θ : ℝ) : ℂ :=
  ∑ n ∈ A, Complex.exp (2 * ↑Real.pi * ↑n * ↑θ * Complex.I)

/-- Erdős Problem #512 (Littlewood's conjecture): There exists an absolute constant C > 0
    such that for every finite set A ⊂ ℤ with |A| ≥ 2,
    ∫₀¹ |∑_{n∈A} e(nθ)| dθ ≥ C · log |A|. -/
theorem erdos_problem_512 :
    ∃ C : ℝ, 0 < C ∧
      ∀ A : Finset ℤ, 2 ≤ A.card →
        C * Real.log (A.card : ℝ) ≤
          ∫ θ in (0 : ℝ)..1, ‖expSum512 A θ‖ :=
  sorry

end
