import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Real

noncomputable section

/-!
# Erdős Problem #237

Let A ⊆ ℕ be a set such that |A ∩ {1,…,N}| ≫ log N for all large N.
Let f(n) count the number of solutions to n = p + a for p prime and a ∈ A.
Is it true that limsup f(n) = ∞?

The answer is yes, as proved by Chen and Ding [ChDi22]. In fact, the
assumption |A ∩ {1,…,N}| ≫ log N can be replaced with just the assumption
that A is infinite. Erdős [Er50] had proved the result when A = {2^k : k ≥ 0}.
-/

/-- The number of representations of n as p + a where p is prime and a ∈ A. -/
def countRepresentations (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | Nat.Prime p ∧ p ≤ n ∧ (n - p) ∈ A}

/-- The counting function |A ∩ {1,…,N}|. -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/--
Erdős Problem #237 [Er55c, Er61, Er73] (proved by Chen–Ding [ChDi22]):

Let A ⊆ ℕ with |A ∩ {1,…,N}| ≥ c · log N for some c > 0 and all
sufficiently large N. Let f(n) = #{p prime : n − p ∈ A} count the
representations of n as prime + element of A. Then limsup f(n) = ∞,
i.e., for every M there exist arbitrarily large n with f(n) ≥ M.
-/
theorem erdos_problem_237 :
    ∀ A : Set ℕ,
    (∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (countingFunction A N : ℝ) ≥ c * Real.log (N : ℝ)) →
    ∀ M : ℕ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ countRepresentations A n ≥ M :=
  sorry

end
