import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

open Nat

noncomputable section

/-!
# Erdős Problem #710

Let f(n) be minimal such that in (n, n+f(n)) there exist distinct integers
a₁, …, aₙ such that k ∣ aₖ for all 1 ≤ k ≤ n. Obtain an asymptotic formula
for f(n).

A problem of Erdős and Pomerance [ErPo80], who proved
  (2/√e + o(1)) · n · (log n / log log n)^{1/2} ≤ f(n)
                                                   ≤ (1.7398… + o(1)) · n · (log n)^{1/2}.

See also [711].

https://www.erdosproblems.com/710
-/

/-- f(n) for Erdős Problem #710: the minimal f such that in the open interval
    (n, n+f) there exist n distinct integers a₁, ..., aₙ with k ∣ aₖ for all
    1 ≤ k ≤ n. -/
noncomputable def erdos710_f (n : ℕ) : ℕ :=
  sInf {f : ℕ | ∃ g : Fin n → ℕ,
    Function.Injective g ∧
    (∀ i : Fin n, n < g i) ∧
    (∀ i : Fin n, g i < n + f) ∧
    (∀ i : Fin n, (i.val + 1) ∣ g i)}

/--
Erdős Problem #710, known lower bound [ErPo80]:

For every ε > 0, there exists N₀ such that for all n ≥ N₀,
  f(n) ≥ (2/√e - ε) · n · (log n / log log n)^{1/2}.
-/
theorem erdos_problem_710_lower :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos710_f n : ℝ) ≥
        (2 / (Real.exp 1) ^ ((1 : ℝ) / 2) - ε) * (n : ℝ) *
        (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) ^ ((1 : ℝ) / 2) :=
  sorry

/--
Erdős Problem #710, known upper bound [ErPo80]:

For every ε > 0, there exists N₀ such that for all n ≥ N₀,
  f(n) ≤ (1.7399 + ε) · n · (log n)^{1/2}.

The constant 1.7398… comes from the original paper; we use 1.7399 as
a rational upper bound on that constant.
-/
theorem erdos_problem_710_upper :
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (erdos710_f n : ℝ) ≤
        (1.7399 + ε) * (n : ℝ) * (Real.log (n : ℝ)) ^ ((1 : ℝ) / 2) :=
  sorry

end
