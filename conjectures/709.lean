import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset

noncomputable section

/-!
# Erdős Problem #709

Let f(n) be minimal such that, for any A = {a₁, …, aₙ} ⊆ [2,∞) ∩ ℕ of size n,
in any interval I of f(n)·max(A) consecutive integers there exist distinct
x₁, …, xₙ ∈ I such that aᵢ ∣ xᵢ.

Obtain good bounds for f(n), or even an asymptotic formula.

A problem of Erdős and Surányi [ErSu59], who proved
  (log n)^c ≪ f(n) ≪ n^{1/2}
for some constant c > 0.

See also [708].

https://www.erdosproblems.com/709
-/

/-- f(n) for Erdős Problem #709: the minimal f such that for any A ⊆ {2,3,...}
    with |A| = n and any interval of f·max(A) consecutive integers starting at k,
    there exist distinct x₁,...,xₙ in the interval with aᵢ ∣ xᵢ.

    Formally, the infimum of all f such that for every such A there exists an
    injective assignment g : A → interval with a ∣ g(a) for all a ∈ A. -/
noncomputable def erdos709_f (n : ℕ) : ℕ :=
  sInf {f : ℕ | ∀ (A : Finset ℕ) (hA : A.Nonempty),
    A.card = n → (∀ a ∈ A, 2 ≤ a) →
    ∀ k : ℕ,
    ∃ g : ℕ → ℕ,
      (∀ a ∈ A, g a ∈ Finset.Icc k (k + f * A.max' hA - 1)) ∧
      (∀ a ∈ A, a ∣ g a) ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, a₁ ≠ a₂ → g a₁ ≠ g a₂)}

/--
Erdős Problem #709, known lower bound [ErSu59]:

There exist constants c > 0 and C > 0 such that for all sufficiently large n,
  f(n) ≥ C · (log n)^c.
-/
theorem erdos_problem_709_lower :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos709_f n : ℝ) ≥ C * (Real.log n) ^ c :=
  sorry

/--
Erdős Problem #709, known upper bound [ErSu59]:

There exist C > 0 and N₀ such that for all n ≥ N₀,
  f(n) ≤ C · n^{1/2}.
-/
theorem erdos_problem_709_upper :
    ∃ C : ℝ, C > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos709_f n : ℝ) ≤ C * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

end
