import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators Classical

/-!
# Erdős Problem #323

Let 1 ≤ m ≤ k and f_{k,m}(x) denote the number of integers ≤ x which are the
sum of m nonnegative k-th powers.

**Part 1**: Is it true that f_{k,k}(x) ≫_ε x^{1-ε} for all ε > 0?

**Part 2**: Is it true that if m < k then f_{k,m}(x) ≫ x^{m/k}
for sufficiently large x?

This would have significant applications to Waring's problem. Erdős and Graham
describe this as 'unattackable by the methods at our disposal'. The case k = 2
was resolved by Landau, who showed f_{2,2}(x) ~ cx/√(log x) for some c > 0.
For k > 2 it is not known if f_{k,k}(x) = o(x).
-/

/-- An integer `n` is a sum of `m` nonnegative `k`-th powers if there exist
    nonnegative integers `a₁, …, aₘ` with `n = a₁^k + ⋯ + aₘ^k`. -/
def IsSumOfKthPowers (k m n : ℕ) : Prop :=
  ∃ a : Fin m → ℕ, n = ∑ i, (a i) ^ k

/-- `f_km k m x` counts the number of natural numbers `≤ x` which can be
    represented as a sum of `m` nonnegative `k`-th powers. -/
noncomputable def f_km (k m x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => IsSumOfKthPowers k m n)).card

/--
**Erdős Problem #323, Part 1** [ErGr80]:

For every k ≥ 1 and ε > 0, f_{k,k}(x) ≫_ε x^{1-ε}, i.e., there exists
a constant C > 0 (depending on k and ε) such that f_{k,k}(x) ≥ C · x^{1-ε}
for all sufficiently large x.
-/
theorem erdos_problem_323a :
    ∀ k : ℕ, 1 ≤ k →
    ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      C * (x : ℝ) ^ (1 - ε) ≤ (f_km k k x : ℝ) :=
  sorry

/--
**Erdős Problem #323, Part 2** [ErGr80]:

For 1 ≤ m < k, f_{k,m}(x) ≫ x^{m/k}, i.e., there exists a constant C > 0
(depending on k and m) such that f_{k,m}(x) ≥ C · x^{m/k} for all
sufficiently large x.
-/
theorem erdos_problem_323b :
    ∀ k : ℕ, 2 ≤ k →
    ∀ m : ℕ, 1 ≤ m → m < k →
    ∃ C : ℝ, 0 < C ∧
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      C * (x : ℝ) ^ ((m : ℝ) / (k : ℝ)) ≤ (f_km k m x : ℝ) :=
  sorry
