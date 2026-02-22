import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #877

Let f_m(n) count the number of maximal sum-free subsets A ⊆ {1, …, n} — that is,
A contains no three elements a, b, c with a = b + c, and A is maximal with this
property (no element of {1, …, n} \ A can be added while preserving sum-freeness).

Is it true that f_m(n) = o(2^{n/2})?

Cameron and Erdős proved that f_m(n) > 2^{n/4}. Luczak and Schoen [LuSc01] proved
that there exists c < 1/2 with f_m(n) < 2^{cn}, resolving the conjecture.
Balogh, Liu, Sharifzadeh, and Treglown [BLST15] proved f_m(n) = 2^{(1/4+o(1))n},
later refined [BLST18] to f_m(n) = (C_n + o(1)) · 2^{n/4}.

https://www.erdosproblems.com/877

Tags: additive combinatorics
-/

/-- A finite set of natural numbers is *sum-free* if for all b, c ∈ A,
    we have b + c ∉ A. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ b ∈ A, ∀ c ∈ A, b + c ∉ A

/-- A subset A of {1, …, n} is a *maximal sum-free subset* if it is sum-free
    and no element of {1, …, n} \ A can be added while preserving sum-freeness. -/
def IsMaximalSumFree (A : Finset ℕ) (n : ℕ) : Prop :=
  A ⊆ Finset.Icc 1 n ∧
  IsSumFree A ∧
  ∀ x ∈ Finset.Icc 1 n, x ∉ A → ¬ IsSumFree (insert x A)

/-- The number of maximal sum-free subsets of {1, …, n}. -/
noncomputable def maximalSumFreeCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => IsMaximalSumFree A n)).card

/--
Erdős Problem #877 [CaEr90][Er98]:

Let f_m(n) count the number of maximal sum-free subsets of {1, …, n}. Then
  f_m(n) = o(2^{n/2}).

That is, for every ε > 0, for all sufficiently large n,
  f_m(n) ≤ ε · 2^{n/2}.

Proved by Luczak and Schoen [LuSc01], with the sharp asymptotics
f_m(n) = 2^{(1/4+o(1))n} established by Balogh–Liu–Sharifzadeh–Treglown [BLST15].
-/
theorem erdos_problem_877 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (maximalSumFreeCount n : ℝ) ≤ ε * (2 : ℝ) ^ ((n : ℝ) / 2) :=
  sorry

end
