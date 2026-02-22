import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

noncomputable section

/-!
# Erdős Problem #989

If A = {z₁, z₂, …} ⊂ ℝ² is an infinite sequence then let
  f(r) = sup_C | |A ∩ C| - π r² |,
where the supremum is over all closed disks C of radius r.

Is f(r) unbounded for every A? How fast does f(r) grow?

This was settled by Beck [Be87], who proved that f(r) ≫ r^{1/2} for all A,
and there exists A such that f(r) ≪ (r log r)^{1/2}.
-/

/-- Euclidean distance in ℝ². -/
noncomputable def euclidDist989 (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- A sequence is locally finite if every closed disk contains only finitely
    many terms of the sequence. -/
def IsLocallyFinite989 (A : ℕ → ℝ × ℝ) : Prop :=
  ∀ (c : ℝ × ℝ) (r : ℝ), Set.Finite {i : ℕ | euclidDist989 (A i) c ≤ r}

/-- Number of terms of A in the closed disk centered at c with radius r. -/
noncomputable def countInDisk989 (A : ℕ → ℝ × ℝ) (c : ℝ × ℝ) (r : ℝ) : ℕ :=
  Set.ncard {i : ℕ | euclidDist989 (A i) c ≤ r}

/-- The discrepancy f(r) = sup over all centers c of | |A ∩ disk(c,r)| - π r² |. -/
noncomputable def discrepancy989 (A : ℕ → ℝ × ℝ) (r : ℝ) : ℝ :=
  ⨆ (c : ℝ × ℝ), |↑(countInDisk989 A c r) - Real.pi * r ^ 2|

/--
Erdős Problem #989, Beck's lower bound [Be87]:
For every locally finite sequence A in ℝ², there exists C > 0 such that
  f(r) ≥ C · √r  for all sufficiently large r.
In particular, f(r) is unbounded for every such A.
-/
theorem erdos_problem_989_lower (A : ℕ → ℝ × ℝ) (hA : IsLocallyFinite989 A) :
    ∃ C : ℝ, C > 0 ∧ ∃ R₀ : ℝ, ∀ r : ℝ, r ≥ R₀ →
      discrepancy989 A r ≥ C * Real.sqrt r :=
  sorry

/--
Erdős Problem #989, Beck's upper bound [Be87]:
There exists a locally finite sequence A in ℝ² and C > 0 such that
  f(r) ≤ C · √(r · log r)  for all sufficiently large r.
-/
theorem erdos_problem_989_upper :
    ∃ (A : ℕ → ℝ × ℝ), IsLocallyFinite989 A ∧
    ∃ C : ℝ, C > 0 ∧ ∃ R₀ : ℝ, ∀ r : ℝ, r ≥ R₀ →
      discrepancy989 A r ≤ C * Real.sqrt (r * Real.log r) :=
  sorry

end
