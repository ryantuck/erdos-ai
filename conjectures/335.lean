import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Classical Filter MeasureTheory

/-- The upper density of A ⊆ ℕ:
  d*(A) = limsup_{N→∞} |A ∩ {0, 1, ..., N-1}| / N -/
noncomputable def upperDensity335 (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- The lower density of A ⊆ ℕ:
  d_*(A) = liminf_{N→∞} |A ∩ {0, 1, ..., N-1}| / N -/
noncomputable def lowerDensity335 (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ))
    Filter.atTop

/-- A set has natural density d if its upper and lower densities both equal d -/
def hasNaturalDensity335 (A : Set ℕ) (d : ℝ) : Prop :=
  upperDensity335 A = d ∧ lowerDensity335 A = d

/--
Erdős Problem #335 [ErGr80, p.51]:

Let d(A) denote the natural density of A ⊆ ℕ. Characterise those A, B ⊆ ℕ
with positive density such that d(A + B) = d(A) + d(B).

One way this can happen is if there exists θ > 0 such that
  A = {n > 0 : fract(nθ) ∈ X_A}  and  B = {n > 0 : fract(nθ) ∈ X_B}
where X_A, X_B ⊆ ℝ/ℤ are measurable with μ(X_A + X_B) = μ(X_A) + μ(X_B).

The conjecture asks whether all such A and B are generated in a similar way
(possibly using other compact abelian groups in place of ℝ/ℤ). We formalize
the specific ℝ/ℤ version of the conjectured characterisation: if d(A+B) = d(A)+d(B)
with positive densities, then A and B arise from measurable subsets of [0,1)
via an irrational rotation, with the corresponding measure additivity property.
-/
theorem erdos_problem_335 :
    ∀ (A B : Set ℕ) (dA dB : ℝ),
      hasNaturalDensity335 A dA →
      hasNaturalDensity335 B dB →
      0 < dA → 0 < dB →
      hasNaturalDensity335 (Set.image2 (· + ·) A B) (dA + dB) →
      ∃ (θ : ℝ) (X_A X_B : Set ℝ),
        0 < θ ∧
        MeasurableSet X_A ∧ MeasurableSet X_B ∧
        X_A ⊆ Set.Ico 0 1 ∧ X_B ⊆ Set.Ico 0 1 ∧
        volume X_A = ENNReal.ofReal dA ∧
        volume X_B = ENNReal.ofReal dB ∧
        volume (Set.image2 (fun a b => Int.fract (a + b)) X_A X_B) =
          volume X_A + volume X_B ∧
        (∀ n : ℕ, 0 < n → (n ∈ A ↔ Int.fract ((n : ℝ) * θ) ∈ X_A)) ∧
        (∀ n : ℕ, 0 < n → (n ∈ B ↔ Int.fract ((n : ℝ) * θ) ∈ X_B)) :=
  sorry
