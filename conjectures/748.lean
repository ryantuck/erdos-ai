import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #748 (Cameron-Erdős Conjecture)

Let f(n) count the number of sum-free subsets A ⊆ {1, …, n}, i.e., A contains
no three elements a, b, c with a = b + c. Is it true that
  f(n) = 2^{(1+o(1)) n/2}?

The lower bound f(n) ≥ 2^{n/2} is trivial (consider all subsets of {⌈n/2⌉,…,n}).

This was proved independently by Green [Gr04] and Sapozhenko [Sa03], who showed
f(n) ~ c_n · 2^{n/2} where c_n depends on the parity of n.

https://www.erdosproblems.com/748

Tags: number theory, combinatorics
-/

/-- A finite set of natural numbers is *sum-free* if it contains no three
    elements a, b, c (not necessarily distinct) with b + c = a. Equivalently,
    for all b, c ∈ A, we have b + c ∉ A. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ b ∈ A, ∀ c ∈ A, b + c ∉ A

/-- The number of sum-free subsets of {1, …, n}. -/
noncomputable def sumFreeSubsetCount (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun A => IsSumFree A)).card

/--
Erdős Problem #748 (Cameron-Erdős Conjecture) [CaEr90][Er94b][Er98]:

Let f(n) count the number of sum-free subsets of {1, …, n}. Then
  f(n) = 2^{(1+o(1)) n/2}.

Equivalently: for every ε > 0, for all sufficiently large n,
  2^{(1 - ε) · n/2} ≤ f(n) ≤ 2^{(1 + ε) · n/2}.

Proved independently by Green [Gr04] and Sapozhenko [Sa03].
-/
theorem erdos_problem_748 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      (2 : ℝ) ^ ((1 - ε) * (n : ℝ) / 2) ≤ (sumFreeSubsetCount n : ℝ) ∧
      (sumFreeSubsetCount n : ℝ) ≤ (2 : ℝ) ^ ((1 + ε) * (n : ℝ) / 2) :=
  sorry

end
