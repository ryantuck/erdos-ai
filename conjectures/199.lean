import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
# Erdős Problem #199

If A ⊂ ℝ does not contain a 3-term arithmetic progression then must
ℝ \ A contain an infinite arithmetic progression?

The answer is no, as shown by Baumgartner [Ba75] (whose construction uses
the axiom of choice to provide a basis for ℝ over ℚ).
-/

/-- A set A ⊆ ℝ contains a 3-term arithmetic progression if there exist
    a, d ∈ ℝ with d ≠ 0 such that a, a + d, a + 2d ∈ A. -/
def HasThreeTermAP (A : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A

/-- A set S ⊆ ℝ contains an infinite arithmetic progression if there exist
    a, d ∈ ℝ with d ≠ 0 such that a + n · d ∈ S for all n : ℕ. -/
def HasInfiniteAP (S : Set ℝ) : Prop :=
  ∃ a d : ℝ, d ≠ 0 ∧ ∀ n : ℕ, (a + ↑n * d) ∈ S

/--
Erdős Problem #199 [Er75b, ErGr79, ErGr80] (DISPROVED):

The original conjecture asked: if A ⊂ ℝ does not contain a 3-term
arithmetic progression, must ℝ \ A contain an infinite arithmetic
progression?

Baumgartner [Ba75] showed the answer is no, using the axiom of choice
to construct a counterexample via a Hamel basis for ℝ over ℚ.
-/
theorem erdos_problem_199 :
    ∃ A : Set ℝ, ¬HasThreeTermAP A ∧ ¬HasInfiniteAP Aᶜ := by
  sorry
