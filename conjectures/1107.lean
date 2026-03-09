import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Nat Finset Classical

noncomputable section

/-!
# Erdős Problem #1107

Let r ≥ 2. A number n is r-powerful if for every prime p which divides n
we have p^r ∣ n. Is every large integer the sum of at most r+1 many
r-powerful numbers?

Given in the 1986 Oberwolfach problem book as a problem of Erdős and Ivić.
This is true when r = 2, as proved by Heath-Brown [He88] (see problem #941).

https://www.erdosproblems.com/1107
Tags: number theory, powerful
-/

/-- A positive natural number n is **r-powerful** if for every prime p dividing n,
we have p^r ∣ n. -/
def IsRPowerful1107 (r : ℕ) (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ r ∣ n

/-- A natural number m is expressible as the sum of at most k many r-powerful numbers. -/
def IsSumOfAtMostRPowerful1107 (r : ℕ) (k : ℕ) (m : ℕ) : Prop :=
  ∃ (j : ℕ) (f : Fin j → ℕ), j ≤ k ∧
    (∀ i, IsRPowerful1107 r (f i)) ∧
    m = ∑ i, f i

/--
Erdős Problem #1107 [Ob1]:

Let r ≥ 2. Is every sufficiently large integer the sum of at most r+1 many
r-powerful numbers?

That is, for each r ≥ 2 there exists N₀ such that for all n ≥ N₀, n can be
written as a sum of at most r+1 many r-powerful numbers.
-/
theorem erdos_problem_1107 (r : ℕ) (hr : 2 ≤ r) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      IsSumOfAtMostRPowerful1107 r (r + 1) n :=
  sorry

end
