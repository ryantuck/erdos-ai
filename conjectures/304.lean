import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open BigOperators Finset Real

noncomputable section

/--
A Finset of natural numbers forms an Egyptian fraction representation of a/b
if all elements are > 1, and a/b = ∑_{n ∈ S} 1/n (as rationals).
-/
def IsEgyptianFractionRepr (a b : ℕ) (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 1 < n) ∧
    (a : ℚ) / (b : ℚ) = ∑ n ∈ S, (1 : ℚ) / (n : ℚ)

/--
Erdős Problem #304 [ErGr80, p.37]:

For integers 1 ≤ a < b, let N(a,b) denote the minimal k such that there exist
integers 1 < n₁ < ⋯ < nₖ with a/b = 1/n₁ + ⋯ + 1/nₖ. Let
N(b) = max_{1 ≤ a < b} N(a,b). Is it true that N(b) ≪ log log b?

Erdős proved that log log b ≪ N(b) ≪ (log b)/(log log b). The upper bound was
improved by Vose (1985) to N(b) ≪ √(log b).
-/
theorem erdos_problem_304 :
    ∃ C : ℝ, 0 < C ∧
      ∀ b : ℕ, 2 ≤ b →
        ∀ a : ℕ, 1 ≤ a → a < b →
          ∃ (S : Finset ℕ),
            IsEgyptianFractionRepr a b S ∧
            (S.card : ℝ) ≤ C * Real.log (Real.log (b : ℝ)) :=
  sorry

end
