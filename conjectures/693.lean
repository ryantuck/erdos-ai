import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real

noncomputable section

/-!
# Erdős Problem #693

Let k ≥ 2 and n be sufficiently large depending on k. Let A = {a₁ < a₂ < ⋯}
be the set of integers in [n, nᵏ] which have a divisor in (n, 2n). Estimate
  max_i (a_{i+1} - a_i).
Is this ≤ (log n)^{O(1)}?

A problem of Erdős [Er79e]. See also [446].
-/

/-- An integer m has a divisor in the open interval (n, 2n). -/
def hasDivisorIn (m n : ℕ) : Prop :=
  ∃ d, d ∣ m ∧ n < d ∧ d < 2 * n

/--
Erdős Problem #693 [Er79e]:

For all k ≥ 2, the maximum gap between consecutive elements of
  A = {m ∈ [n, nᵏ] : m has a divisor in (n, 2n)}
is at most (log n)^C for some constant C, for all sufficiently large n.
-/
theorem erdos_problem_693 :
    ∀ k : ℕ, k ≥ 2 →
    ∃ C : ℕ,
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ a b : ℕ, n ≤ a → a < b → b ≤ n ^ k →
    hasDivisorIn a n → hasDivisorIn b n →
    (∀ m : ℕ, a < m → m < b → ¬hasDivisorIn m n) →
    (b : ℝ) - (a : ℝ) ≤ (Real.log (n : ℝ)) ^ C :=
  sorry

end
