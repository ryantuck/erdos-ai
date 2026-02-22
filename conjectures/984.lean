import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

/-!
# Erdős Problem #984

Can ℕ be 2-coloured such that if {a, a+d, …, a+(k-1)d} is a k-term
monochromatic arithmetic progression then k ≪_ε a^ε for all ε > 0?

A question of Spencer, who proved that this is possible with 3 colours,
with a^ε replaced by a very slowly growing function h(a) (the inverse of
the van der Waerden function). Erdős reports that he can construct such a
colouring with the bound k ≪ a^{1-c} for some absolute constant c > 0.

Zach Hunter proved that the answer is yes.
-/

/-- An arithmetic progression {a, a+d, …, a+(k-1)d} is monochromatic under
    colouring c if all its elements receive the same colour. -/
def IsMonochromaticAP (c : ℕ → Fin 2) (a d k : ℕ) : Prop :=
  d ≥ 1 ∧ k ≥ 1 ∧ ∃ color : Fin 2, ∀ i : ℕ, i < k → c (a + i * d) = color

/--
Erdős Problem #984 [Er80]:

There exists a 2-colouring of ℕ such that for every ε > 0, there is a
constant C > 0 such that every k-term monochromatic arithmetic progression
{a, a+d, …, a+(k-1)d} with a ≥ 1 satisfies k ≤ C · a^ε.
-/
theorem erdos_problem_984 :
    ∃ c : ℕ → Fin 2, ∀ ε : ℝ, ε > 0 →
      ∃ C : ℝ, C > 0 ∧ ∀ a d k : ℕ, a ≥ 1 →
        IsMonochromaticAP c a d k →
          (k : ℝ) ≤ C * (a : ℝ) ^ ε :=
  sorry

end
