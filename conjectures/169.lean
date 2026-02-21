import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset BigOperators Real

/-- A finset of natural numbers is k-AP-free if it contains no arithmetic
progression of length k with positive common difference. -/
def IsAPFree (k : ℕ) (A : Finset ℕ) : Prop :=
  ¬∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A

/-- The van der Waerden property: every 2-coloring of {0, ..., N-1} contains
a monochromatic k-term arithmetic progression. -/
def VDWProperty (k N : ℕ) : Prop :=
  ∀ f : ℕ → Bool, ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
    ∀ i : ℕ, i < k → f (a + i * d) = f a

/-- Van der Waerden's theorem guarantees the existence of W(k) for all k. -/
lemma vdw_exists (k : ℕ) : ∃ N, VDWProperty k N := by sorry

open Classical in
/-- The van der Waerden number W(k): the smallest N such that any 2-coloring
of {0, ..., N-1} contains a monochromatic k-term AP. -/
noncomputable def vanDerWaerdenNumber (k : ℕ) : ℕ :=
  Nat.find (vdw_exists k)

/--
Erdős Problem #169:
Let k ≥ 3 and f(k) be the supremum of ∑_{n ∈ A} 1/n over all sets A of
positive integers containing no k-term arithmetic progression.

Is lim_{k → ∞} f(k) / log W(k) = ∞, where W(k) is the van der Waerden number?

This is formalized as: for every constant C > 0, for all sufficiently large k,
there exists a finite AP-free set A of positive integers whose reciprocal sum
exceeds C · log W(k).
-/
theorem erdos_problem_169_conjecture :
    ∀ C : ℝ, 0 < C → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ A : Finset ℕ, (∀ n ∈ A, 0 < n) ∧ IsAPFree k A ∧
        C * Real.log (↑(vanDerWaerdenNumber k) : ℝ) <
          ∑ n ∈ A, (1 : ℝ) / (↑n : ℝ) :=
  sorry
