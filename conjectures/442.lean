import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

open BigOperators Finset Filter Real

noncomputable section

/-- The reciprocal sum of A ∩ [1, x): ∑_{n ∈ A ∩ [1,x)} 1/n. -/
def reciprocalSum (A : Finset ℕ → Finset ℕ) (x : ℕ) : ℝ :=
  ∑ n ∈ A (Finset.range x), (1 : ℝ) / (n : ℝ)

/-- The lcm pair sum over A ∩ [1,x):
  ∑_{a,b ∈ A ∩ [1,x), a < b} 1/lcm(a,b). -/
def lcmPairRawSum (A : Finset ℕ → Finset ℕ) (x : ℕ) : ℝ :=
  let S := A (Finset.range x)
  ∑ a ∈ S, ∑ b ∈ S.filter (· > a), (1 : ℝ) / (Nat.lcm a b : ℝ)

/--
Erdős Problem #442 [ErGr80, p.88] (DISPROVED):

Is it true that if A ⊆ ℕ is such that
  (1 / log log x) · ∑_{n ∈ A ∩ [1,x)} 1/n → ∞
then
  (∑_{n ∈ A ∩ [1,x)} 1/n)⁻² · ∑_{a,b ∈ A ∩ (1,x], a < b} 1/lcm(a,b) → ∞?

Tao [Ta24b] disproved this: there exists A ⊂ ℕ whose reciprocal sum grows
like exp((1/2 + o(1)) √(log log x) · log log log x), yet the normalized
lcm pair sum remains bounded. Moreover, Tao shows this growth rate is
sharp: any faster growth forces the normalized lcm pair sum to diverge.
-/
theorem erdos_problem_442 :
    ∃ A : Finset ℕ → Finset ℕ,
      (∀ S : Finset ℕ, A S ⊆ S) ∧
      (∀ C : ℝ, ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        C * Real.log (Real.log (x : ℝ)) ≤ reciprocalSum A x) ∧
      (∃ M : ℝ, ∀ x : ℕ,
        lcmPairRawSum A x ≤ M * (reciprocalSum A x) ^ 2) :=
  sorry

end
